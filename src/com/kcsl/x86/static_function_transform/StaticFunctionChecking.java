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
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

public class StaticFunctionChecking {
	
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

		
		Map<Integer, Node> headerIDMapping = new HashMap<Integer, Node>();
		
		//List to hold all static roots that have leaves added, make sure we don't add duplicate edges
		ArrayList<Node> leavesAdded = new ArrayList<Node>();
		
		//Map to hold node names for all nodes that are callsites to static functions for a given
		//source function and their respective CFGs
		Map<String, Q> staticCFG = new HashMap<String, Q>();
		Map<Integer, Node> recreatedNodes = new HashMap<Integer, Node>();
		
		//Map to hold static cfg root and the leaves for ease of edge addition for leaves to successor
		Map<Node, ArrayList<Node>> leavesMap = new HashMap<Node, ArrayList<Node>>();
		
		Node container = cfg.containers().nodes(XCSG.C.TranslationUnit).eval().nodes().one();
		String containerName = container.getAttr(XCSG.name).toString();
		
		//Get all the static cfgs found in the graph to easily remake 
		for (Node y : dfg) {
			String staticName = Common.toQ(y).containers().nodes(XCSG.C.TranslationUnit).eval().nodes().one().getAttr(XCSG.name).toString();
			String nodeName = y.getAttr(XCSG.name).toString();
			nodeName = nodeName.replace("...", "");
			nodeName += ";";
			
			Q b = bcfg(y.getAttr(XCSG.name).toString().split("\\(")[0]);
			String bContainer = b.containers().nodes(XCSG.C.TranslationUnit).eval().nodes().one().getAttr(XCSG.name).toString(); 
			
			if (!staticCFG.containsKey(nodeName) && staticName.equals(containerName) && staticName.equals(bContainer)) {
				staticCFG.put(nodeName, b);
			}
		}

		Node functionNode = Graph.U.createNode();
		functionNode.putAttr(XCSG.name, "static_transform_"+functionName);
		functionNode.tag(XCSG.Function);
		

		for (Edge e : cfg.eval().edges()) {
			Node eFrom = e.from();
			Node eTo = e.to();
			
			String fromFunctionNode = e.from().getAttr(XCSG.name).toString().split("\\(")[0];
			fromFunctionNode += "();";
			String toNode = e.to().getAttr(XCSG.name).toString().split("\\(")[0];
			toNode += "();";
			
			//Need to handle when the return value of a function is used in a variable assignment
			if (fromFunctionNode.contains("=")) {
				fromFunctionNode = fromFunctionNode.split("=")[1];
				fromFunctionNode = fromFunctionNode.split(" ")[1];
				if (!staticCFG.containsKey(fromFunctionNode)) {
					fromFunctionNode = eFrom.getAttr(XCSG.name).toString();
				}
			}else if(!staticCFG.containsKey(fromFunctionNode)) {
				fromFunctionNode = eFrom.getAttr(XCSG.name).toString();
			}
			
			if (toNode.contains("=")) {
				toNode = toNode.split("=")[1];
				toNode = toNode.split(" ")[1];
				if (!staticCFG.containsKey(toNode)) {
					toNode = eTo.getAttr(XCSG.name).toString();
				}
			}else if(!staticCFG.containsKey(toNode)) {
				toNode = eTo.getAttr(XCSG.name).toString();
			}
			
			//Handle the case where we have consecutive static function calls
			if (staticCFG.containsKey(fromFunctionNode) && staticCFG.containsKey(toNode)) {
				
				Node root = null;
				Node root2 = null;
				Q fromFunction = staticCFG.get(fromFunctionNode);
				Q toFunction = staticCFG.get(toNode);
				
				Node firstGraphCheck = headerIDMapping.get(eFrom.addressBits());
				if (firstGraphCheck != null) {
					root = recreatedNodes.get(firstGraphCheck.addressBits());
				}
				else {
					root = createStaticCFG(toFunction,functionNode,recreatedNodes, leavesMap, containerName);
					headerIDMapping.put(eFrom.addressBits(), root);
				}
				
				//get root of second graph for destination of leaves from first graph
				Node secondGraphCheck = headerIDMapping.get(eTo.addressBits());
				if (secondGraphCheck != null) {
					root2 = recreatedNodes.get(secondGraphCheck.addressBits());
				}
				else {
					root2 = createStaticCFG(fromFunction,functionNode,recreatedNodes, leavesMap, containerName);
					headerIDMapping.put(eTo.addressBits(), root2);
				}
				
				if(!leavesAdded.contains(root)) {
					addLeafEdges(root, root2, e, leavesMap);
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
				String toCheckName = successor.getAttr(XCSG.name).toString();
				toCheckName = toCheckName.split("\\(")[0];
				toCheckName += "();";
				
				if (toCheckName.contains("=")) {
					toCheckName = toCheckName.split("=")[1];
					toCheckName = toCheckName.split(" ")[1];
					if (!staticCFG.containsKey(toCheckName)) {
						toCheckName = successor.getAttr(XCSG.name).toString();
					}
				}else if(!staticCFG.containsKey(toCheckName)) {
					toCheckName = successor.getAttr(XCSG.name).toString();				
				}
				
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
						Q successorFunction = staticCFG.get(toCheckName);
						toCheck = createStaticCFG(successorFunction,functionNode,recreatedNodes, leavesMap, containerName);
						headerIDMapping.put(successor.addressBits(), toCheck);
					}
				}

				Q sFunction = staticCFG.get(toNode);				
				Node root = createStaticCFG(sFunction,functionNode,recreatedNodes, leavesMap, containerName);
				createEdge(e, fromCheck, root);
				headerIDMapping.put(eTo.addressBits(), root);
				
				if(!leavesAdded.contains(root)) {
					addLeafEdges(root, toCheck, e, leavesMap);
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
						addLeafEdges(root, dest, e, leavesMap);
						leavesAdded.add(root);
					}
					continue;
				}
				
				Node successor = e.to();
				Node toCheck = recreatedNodes.get(successor.addressBits());
				
				String toCheckName = successor.getAttr(XCSG.name).toString();
				toCheckName = toCheckName.split("\\(")[0];
				toCheckName += "();";
				
				if (toCheckName.contains("=")) {
					toCheckName = toCheckName.split("=")[1];
					toCheckName = toCheckName.split(" ")[1];
					if (!staticCFG.containsKey(toCheckName)) {
						toCheckName = successor.getAttr(XCSG.name).toString();
					}
				}else if(!staticCFG.containsKey(toCheckName)) {
					toCheckName = successor.getAttr(XCSG.name).toString();				
				}
				
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
						Q successorFunction = staticCFG.get(toCheckName);
						toCheck = createStaticCFG(successorFunction,functionNode,recreatedNodes, leavesMap, containerName);
						headerIDMapping.put(successor.addressBits(), toCheck);
					}
				}
				
				Q sFunction = staticCFG.get(fromFunctionNode);
				Node root = createStaticCFG(sFunction,functionNode,recreatedNodes, leavesMap, containerName);

				headerIDMapping.put(eFrom.addressBits(), root);
				if(!leavesAdded.contains(root)) {
					addLeafEdges(root, toCheck, e, leavesMap);
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
			if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
				cfgEdge.putAttr(XCSG.conditionValue, true);
				cfgEdge.putAttr(XCSG.name, "true");
			}else {
				cfgEdge.putAttr(XCSG.conditionValue, false);
				cfgEdge.putAttr(XCSG.name, "false");
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
	 * 		Function node for the new graph that will be returned, used to add container edges
	 * @param recreatedNodes
	 * 		Map of nodes that have already been recreated for the graph that will be returned. 
	 * 		We want to add all of the nodes created here to that map. Key is the address bits of the
	 * 		created node and value is the node itself
	 * @param leafMapping
	 * 		Map of created static CFG roots and their associated leaves, used
	 * 		for ease of edge creation and iteration. Roots and their leaves are added here
	 * @param container
	 * 		Translation Unit name for the parent C file to ensure that we are getting the correct static function
	 * @return
	 * 		Returns the root of the static CFG created
	 */
	
	
	public static Node createStaticCFG(Q sFunction, Node functionNode, Map<Integer, Node> recreatedNodes, Map<Node, ArrayList<Node>> leafMapping, String container) {
		
		Node root = null;
		Map<Integer, Node> tempTracking = new HashMap<Integer, Node>();
		ArrayList<Node> tempMapping = new ArrayList<Node>();

		for(Edge eStatic : sFunction.eval().edges()) {
			
			//Need to make sure that we don't get a different static funciton with the same name
			String eContainer = Common.toQ(eStatic.from()).containers().nodes(XCSG.C.TranslationUnit).eval().nodes().one().getAttr(XCSG.name).toString();
			if (!container.equals(eContainer)) {
				continue;
			}
			
			Node from = tempTracking.get(eStatic.from().addressBits());
			Node to = tempTracking.get(eStatic.to().addressBits());
			
			if (from == null) {
				 from = createNode(eStatic.from(), true, functionNode);
				 recreatedNodes.put(from.addressBits(), from);
				 tempTracking.put(eStatic.from().addressBits(), from);
			}
			if (to == null) {
				to = createNode(eStatic.to(), true, functionNode);
				recreatedNodes.put(to.addressBits(), to);
				tempTracking.put(eStatic.to().addressBits(), to);
				
				if (eStatic.to().taggedWith(XCSG.controlFlowExitPoint)) {
					to.tag("static_leaf");
					tempMapping.add(to);
				}
			}
			
			if (from.taggedWith(XCSG.controlFlowRoot)) {
				root = from;
			}else if (to.taggedWith(XCSG.controlFlowRoot)) {
				root = to;
			}
			createEdge(eStatic, from, to);					
		}
		leafMapping.put(root, tempMapping);
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
	
	public static void addLeafEdges(Node root, Node dest, Edge e, Map<Node, ArrayList<Node>> leafMapping) {
		ArrayList<Node> tempMapping = new ArrayList<Node>();		
		tempMapping = leafMapping.get(root);
		for (Node l : tempMapping) {
			l.untag(XCSG.controlFlowExitPoint);
			createEdge(e, l, dest);
		}

	}

}
