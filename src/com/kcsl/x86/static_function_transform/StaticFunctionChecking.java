package com.kcsl.x86.static_function_transform;

import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;
import static com.kcsl.x86.support.SupportMethods.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IFile;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.index.common.SourceCorrespondence;
//import com.ensoftcorp.atlas.core.index.common.SourceCorrespondence;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

public class StaticFunctionChecking {
	
	//Map to hold node names for all nodes that are callsites to static functions for a given
	//source function and their respective CFGs
	private static Map<String, Q> staticCFG;
	private static Map<Integer, Node> recreatedNodes;
	private static String containerName;
	//Map to hold static cfg root and the leaves for ease of edge addition for leaves to successor
	private static Map<Node, ArrayList<Node>> leavesMap;
	
	public static ArrayList<Node> staticChecker() {
			
		ArrayList<Node> staticFunctions = new ArrayList<Node>();		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.C.Provisional.internalLinkage);
		
		for (Node f : functions.eval().nodes()) {
			if (!staticFunctions.contains(f)) {
				staticFunctions.add(f);
			}
		}		
		
		return staticFunctions;
	}
	
	public static Q staticTransform(String functionName) {
		
		Q f = my_function(functionName);
		Q cfg = my_cfg(f);
		ArrayList<Node> dfg = my_dataFlow(functionName);
		
		//Return the original CFG if no static functions found
		if (dfg.size() == 0) {
			return cfg;
		}
		
		//Map to keep track of static callsite and root of created graph
		Map<Integer, Node> headerIDMapping = new HashMap<Integer, Node>();
		
		//List to hold all static roots that have leaves added, make sure we don't add duplicate edges
		ArrayList<Node> leavesAdded = new ArrayList<Node>();
		
		
		staticCFG = new HashMap<String, Q>();
		recreatedNodes = new HashMap<Integer, Node>();
		leavesMap = new HashMap<Node, ArrayList<Node>>();
		
		Node container = cfg.containers().nodes(XCSG.C.TranslationUnit).eval().nodes().one();
		containerName = container.getAttr(XCSG.name).toString();
		
		//Get all the static cfgs found in the graph to easily remake 
		for (Node y : dfg) {
			String staticName = Common.toQ(y).containers().nodes(XCSG.C.TranslationUnit).eval().nodes().one().getAttr(XCSG.name).toString();
			String nodeName = y.getAttr(XCSG.name).toString();
			String sFuncName = y.getAttr(XCSG.name).toString().split("\\(")[0];
			nodeName = nodeName.replace("...", "");
			nodeName += ";";
			
			Q b = staticCFGFinder(containerName, sFuncName);
			if (!staticCFG.containsKey(nodeName) && staticName.equals(containerName)) {
				staticCFG.put(nodeName, b);
			}
		}

		Node functionNode = Graph.U.createNode();
		functionNode.putAttr(XCSG.name, "static_transform_"+functionName);
		functionNode.tag(XCSG.Function);
		

		for (Edge e : cfg.eval().edges()) {
			Node eFrom = e.from();
			Node eTo = e.to();
			
			String fromFunctionNode = createNodeName(e.from());
			String toNode = createNodeName(e.to());
			
			//Handle the case where we have consecutive static function calls
			if (staticCFG.containsKey(fromFunctionNode) && staticCFG.containsKey(toNode)) {
				
				Node root = null;
				Node root2 = null;
				
				Node firstGraphCheck = headerIDMapping.get(eFrom.addressBits());
				if (firstGraphCheck != null) {
					root = recreatedNodes.get(firstGraphCheck.addressBits());
				}
				else {
					root = createStaticCFG(toNode,functionNode, headerIDMapping);
					headerIDMapping.put(eFrom.addressBits(), root);
				}
				
				//get root of second graph for destination of leaves from first graph
				Node secondGraphCheck = headerIDMapping.get(eTo.addressBits());
				if (secondGraphCheck != null) {
					root2 = recreatedNodes.get(secondGraphCheck.addressBits());
				}
				else {
					root2 = createStaticCFG(fromFunctionNode,functionNode, headerIDMapping);
					headerIDMapping.put(eTo.addressBits(), root2);
				}
				
				if(!leavesAdded.contains(root)) {
					addLeafEdges(root, root2, e);
					leavesAdded.add(root);
				}
				continue;
			}
			//Handle the case where we point to a static call site
			else if (staticCFG.containsKey(toNode)) {
				Node fromCheck = recreatedNodes.get(e.from().addressBits());
				if (fromCheck == null) {
					fromCheck = createNode(e.from(), false, functionNode);
					recreatedNodes.put(e.from().addressBits(), fromCheck);
					
					fromCheck.tag("static_transform");
					Edge tempEdge = Graph.U.createEdge(functionNode, fromCheck);
					tempEdge.tag(XCSG.Contains);
				}
				
				//Check to make sure we haven't already made the static CFG
				Node graphCheck = headerIDMapping.get(eTo.addressBits());
				if (graphCheck != null) {

					//If graph has already been made, just add edges from predecessor to root
					Node root = recreatedNodes.get(graphCheck.addressBits());
					createEdge(e, fromCheck, root);
					continue;
				}
				
				Node successor = e.to().out(XCSG.ControlFlow_Edge).one().to();
				Node toCheck = recreatedNodes.get(successor.addressBits());
				String toCheckName = createNodeName(successor);
				toCheck = createSuccessorEdges(toCheck, toCheckName, functionNode, successor, headerIDMapping);
				
				Node root = createStaticCFG(toNode,functionNode, headerIDMapping);
				createEdge(e, fromCheck, root);
				headerIDMapping.put(eTo.addressBits(), root);
				
				if(!leavesAdded.contains(root)) {
					addLeafEdges(root, toCheck, e);
					leavesAdded.add(root);
				}
			}
			//Handle the case where the from node for the edge is a static function call
			else if (staticCFG.containsKey(fromFunctionNode)) {
				
				//Check to see if we've already created the static CFG
				if (headerIDMapping.containsKey(e.from().addressBits())) {
					
					//If graph has already been made, just add edges to from leaves to successor
					String fromName = e.from().getAttr(XCSG.name).toString();
					fromName = fromName.split("\\(")[0];
					fromName += "();";
					
					Q sCFG = staticCFG.get(fromName);
					Node dest = recreatedNodes.get(e.to().addressBits());
					if (dest == null) {
						dest = createNode(e.to(), false, functionNode);
						recreatedNodes.put(e.to().addressBits(), dest);
						
						dest.tag("static_transform");
						Edge tempEdge = Graph.U.createEdge(functionNode, dest);
						tempEdge.tag(XCSG.Contains);
					}
					
					Node root = headerIDMapping.get(e.from().addressBits());
					if(!leavesAdded.contains(root)) {
						addLeafEdges(root, dest, e);
						leavesAdded.add(root);
					}
					continue;
				}
				
				Node successor = e.to();
				Node toCheck = recreatedNodes.get(successor.addressBits());
				String toCheckName = createNodeName(successor);
				toCheck = createSuccessorEdges(toCheck, toCheckName, functionNode, successor, headerIDMapping);
				Node root = createStaticCFG(fromFunctionNode,functionNode, headerIDMapping);

				headerIDMapping.put(eFrom.addressBits(), root);
				if(!leavesAdded.contains(root)) {
					addLeafEdges(root, toCheck, e);
					leavesAdded.add(root);
				}

			}
			//Handle all other CFG nodes 
			else {
				Node from = createNode(e.from(), false, functionNode);
				Node to = createNode(e.to(), false, functionNode);
				
				Node fromCheck = recreatedNodes.get(e.from().addressBits());
				Node toCheck = recreatedNodes.get(e.to().addressBits());
				
				if (fromCheck == null && toCheck == null) {
					recreatedNodes.put(e.from().addressBits(), from);
					recreatedNodes.put(e.to().addressBits(), to);	
					createEdge(e, from, to);
					
					
					from.tag("static_transform");
					Edge fromEdge = Graph.U.createEdge(functionNode, from);
					fromEdge.tag(XCSG.Contains);
					
					
					to.tag("static_transform");
					Edge toEdge = Graph.U.createEdge(functionNode, to);
					toEdge.tag(XCSG.Contains);
				}
				else if (fromCheck != null && toCheck == null) {
					recreatedNodes.put(e.to().addressBits(), to);	
					createEdge(e, fromCheck, to);
					
					to.tag("static_transform");
					Edge toEdge = Graph.U.createEdge(functionNode, to);
					toEdge.tag(XCSG.Contains);
				}
				else if (fromCheck == null && toCheck != null) {
					recreatedNodes.put(e.from().addressBits(), from);	
					createEdge(e, from, toCheck);
					
					from.tag("static_transform");
					Edge fromEdge = Graph.U.createEdge(functionNode, from);
					fromEdge.tag(XCSG.Contains);
				}
				else if (fromCheck != null && toCheck != null) {
					createEdge(e, fromCheck, toCheck);
				}
			}
		}
		
		
		Q x = my_function(functionNode.getAttr(XCSG.name).toString());
		Q static_cfg = my_cfg(x);
		return static_cfg.nodes("static_transform").induce(Query.universe().edges("static_edge"));
		
	}
	
	
	/**
	 * Method used to ease the creation of nodes that will be added to returned graph
	 * @param original
	 * 		Node from the original CFG that we are recreating
	 * @param check
	 * 		Used to determine if these are nodes for a static CFG that need to be tagged
	 * @param function
	 * 		Function node for returned graph to add container edges
	 * @return
	 * 		Returns the new created node
	 */
	
	public static Node createNode(Node original, boolean check, Node function) {
		Node returnNode = null;
		
		Iterable<String> tags = original.tagsI();
		returnNode = Graph.U.createNode();
		String name = original.getAttr(XCSG.name).toString();
		
		returnNode.putAttr(XCSG.name, name);
		for (String s : tags) {
			returnNode.tag(s);
		}
		
		//Adding source correspondence for switch statement transform
		SourceCorrespondence c = (SourceCorrespondence) original.getAttr(XCSG.sourceCorrespondence);
		returnNode.putAttr(XCSG.sourceCorrespondence, c);
		
		//Handling the case when there are logical operators for short circuit transform
		AtlasSet<Node> containerNodes = Common.toQ(original).contained().nodes(XCSG.LogicalAnd, XCSG.LogicalOr).eval().nodes();
		if (containerNodes.size() > 0) {
			for (Node n : containerNodes) {
				Iterable<String> containerTags = n.tagsI();
				Node dataNode = Graph.U.createNode();
				String dName = n.getAttr(XCSG.name).toString();
				dataNode.putAttr(XCSG.name, dName);
				for (String t : containerTags) {
					dataNode.tag(t);
				}
				dataNode.tag("static_transform");
				Edge containerEdge = Graph.U.createEdge(returnNode, dataNode);
				containerEdge.tag(XCSG.Contains);
				containerEdge.tag("switch_edge");
				
				Edge functionContainer = Graph.U.createEdge(function, dataNode);
				functionContainer.tag(XCSG.Contains);
				functionContainer.tag("static_edge");
			}
		}
		
		if (check) {
			Edge toEdge = Graph.U.createEdge(function, returnNode);
			toEdge.tag(XCSG.Contains);
			returnNode.tag("static_transform");
		}
		return returnNode;
	}
	
	public static void createEdge(Edge e, Node f, Node t) {
		Edge cfgEdge = Graph.U.createEdge(f, t);
		cfgEdge.tag(XCSG.ControlFlow_Edge);
		cfgEdge.tag("static_edge");
		
		if (e.hasAttr(XCSG.conditionValue)) {
			String conditionVal = e.getAttr(XCSG.conditionValue).toString();
			cfgEdge.putAttr(XCSG.conditionValue, conditionVal);
			if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
				cfgEdge.putAttr(XCSG.name, "true");
			}else if (e.getAttr(XCSG.conditionValue).toString().contains("false")){
				cfgEdge.putAttr(XCSG.name, "false");
			}else if (e.getAttr(XCSG.conditionValue).toString().contains("default")) {
				cfgEdge.putAttr(XCSG.name, "default");
			}
		}
		
		if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
			cfgEdge.tag(XCSG.ControlFlowBackEdge);
		}
	}
	
	
	/**
	 * Method used to create the static CFGs that will replace each static function call 
	 * in a given funciton
	 * @param sFunction
	 * 		CFG for the original static function 
	 * @param functionNode
	 * @return
	 * 		Returns the root of the static CFG created
	 */
	
	
	public static Node createStaticCFG(String sFunctionName, Node functionNode, Map<Integer, Node> headerIDMapping) {
		
		Q sFunction = staticCFG.get(sFunctionName);
		Node root = null;
		Map<Integer, Node> tempTracking = new HashMap<Integer, Node>();
		ArrayList<Node> tempMapping = new ArrayList<Node>();
		boolean edgeCheck;
		boolean staticCheck; 

		for(Edge eStatic : sFunction.eval().edges()) {
			
			//Need to make sure that we don't get a different static funciton with the same name
			String eContainer = Common.toQ(eStatic.from()).containers().nodes(XCSG.C.TranslationUnit).eval().nodes().one().getAttr(XCSG.name).toString();
			if (!containerName.equals(eContainer)) {
				continue;
			}
			
			edgeCheck = true;
			staticCheck = false;
			String fromName = createNodeName(eStatic.from());
			String toName = createNodeName(eStatic.to());
			Node from = tempTracking.get(eStatic.from().addressBits());
			Node to = tempTracking.get(eStatic.to().addressBits());
			
			//Check for nested static function calls
			if (from == null && !staticCFG.containsKey(fromName)) {
				from = createNode(eStatic.from(), true, functionNode);
				from.tag(sFunctionName);
				recreatedNodes.put(from.addressBits(), from);
				tempTracking.put(eStatic.from().addressBits(), from);
			}
			else if (from == null && staticCFG.containsKey(fromName)) {
				//Recurse if we find another static function
				from = createStaticCFG(fromName, functionNode, headerIDMapping);
				tempTracking.put(eStatic.from().addressBits(), from);
				edgeCheck = false;		
			}
			else if (from != null && staticCFG.containsKey(fromName)) {
				//Handle the case where we are coming from a nested function
				edgeCheck = false;
				staticCheck = true;
			}
			
			if (to == null && !staticCFG.containsKey(toName)) {
				to = createNode(eStatic.to(), true, functionNode);
				to.tag(sFunctionName);
				recreatedNodes.put(to.addressBits(), to);
				tempTracking.put(eStatic.to().addressBits(), to);
				
				if (eStatic.to().taggedWith(XCSG.controlFlowExitPoint)) {
					to.tag("static_leaf");
					tempMapping.add(to);
				}
			}
			else if (to == null && staticCFG.containsKey(toName)) {
				to = createStaticCFG(toName, functionNode, headerIDMapping);
				tempTracking.put(eStatic.to().addressBits(), to);
			}
			
			
			if (from.taggedWith(XCSG.controlFlowRoot) && from.taggedWith(sFunctionName)) {
				root = from;
			}else if (to.taggedWith(XCSG.controlFlowRoot) && to.taggedWith(sFunctionName)) {
				root = to;
			}
			//Check to see if we need to add continuation edges from another static call
			if (edgeCheck) {
				createEdge(eStatic, from, to);
			}else {
				if (!staticCheck) {
					addLeafEdges(from, to, eStatic);
				}else {
					//If from node is a nested call, we need to add edges from all
					//leaves to successor
					ArrayList<Node> leaves = leavesMap.get(from);
					for (Node staticLeaf : leaves) {
						createEdge(eStatic, staticLeaf, to);
					}
				}
			}
		}
		leavesMap.put(root, tempMapping);
		return root;
	}
	
	
	/**
	 * Method used to create the edges between all of the leaf nodes for a 
	 * static CFG to the correct successor
	 * @param root
	 * 		Root of the static CFG call we are trying add the edges for
	 * @param dest
	 * 		Node that we want all of the leaf nodes to point to
	 * @param e
	 * 		The original CFG edge, used to add any tags/conditional values
	 * @param leafMapping
	 * 		Map of created static CFG roots and their associated leaves, used
	 * 		for ease of edge creation and iteration
	 */
	
	public static void addLeafEdges(Node root, Node dest, Edge e) {
		ArrayList<Node> tempMapping = new ArrayList<Node>();		
		tempMapping = leavesMap.get(root);
		for (Node l : tempMapping) {
			l.untag(XCSG.controlFlowExitPoint);
			createEdge(e, l, dest);
		}

	}
	
	public static Node createSuccessorEdges(Node toCheck, String toCheckName, Node functionNode, Node successor, Map<Integer, Node> headerIDMapping) {
		
		if (toCheck == null && !staticCFG.containsKey(toCheckName)) {
			toCheck = createNode(successor, false, functionNode);
			recreatedNodes.put(successor.addressBits(), toCheck);
			
			toCheck.tag("static_transform");
			Edge tempToEdge = Graph.U.createEdge(functionNode, toCheck);
			tempToEdge.tag(XCSG.Contains);
		}
		else if (toCheck == null && staticCFG.containsKey(toCheckName)){
			Node successorCheck = headerIDMapping.get(successor.addressBits());
			if (successorCheck == null) {
				toCheck = createStaticCFG(toCheckName,functionNode, headerIDMapping);
				headerIDMapping.put(successor.addressBits(), toCheck);
			}
		}
		
		return toCheck;
		
	}
	
	public static String createNodeName(Node n) {
		
		String nodeName = n.getAttr(XCSG.name).toString().split("\\(")[0];
		nodeName += "();";
		
		//Need to handle when the return value of a function is used in a variable assignment
		if (nodeName.contains("=")) {
			nodeName = nodeName.split("=")[1];
			nodeName = nodeName.split(" ")[1];
			if (!staticCFG.containsKey(nodeName)) {
				nodeName = n.getAttr(XCSG.name).toString();
			}
		}else if(!staticCFG.containsKey(nodeName)) {
			nodeName = n.getAttr(XCSG.name).toString();
		}
		
		return nodeName;
	}

}
