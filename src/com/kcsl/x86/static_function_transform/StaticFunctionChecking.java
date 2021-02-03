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
		
		//ArrayList to hold nodes to all static functions in code base
		ArrayList<Node> staticFunctions = staticChecker();
		
		//Map to hold node names for all nodes that are callsites to static functions for a given
		//source function and their respective CFGs
		Map<String, Q> staticCFG = new HashMap<String, Q>();

		Node container = cfg.containers().nodes(XCSG.C.TranslationUnit).eval().nodes().one();
		String containerName = container.getAttr(XCSG.name).toString();
		
		for (Node y : dfg) {
			String staticName = Common.toQ(y).containers().nodes(XCSG.C.TranslationUnit).eval().nodes().one().getAttr(XCSG.name).toString();
			String nodeName = y.getAttr(XCSG.name).toString();
			nodeName = nodeName.replace("...", "");
			nodeName += ";";
			
			if (!staticCFG.containsKey(nodeName) && staticName.equals(containerName)) {
				Q b = bcfg(y.getAttr(XCSG.name).toString().split("\\(")[0]);
				System.out.println(b.eval().edges().size());
				staticCFG.put(nodeName, b);
			}
		}

		Node functionNode = Graph.U.createNode();
		functionNode.putAttr(XCSG.name, "static_transform_"+functionName);
		functionNode.tag(XCSG.Function);
		
		Map<Node, Node> recreatedNodes = new HashMap<Node, Node>();
		ArrayList<staticHeaderNode> headerNodes = new ArrayList<staticHeaderNode>();
		
		for (Edge e : cfg.eval().edges()) {
			Node eFrom = e.from();
			Node eTo = e.to();
			
			String fromFunctionNode = e.from().getAttr(XCSG.name).toString().split("\\(")[0];
			fromFunctionNode += "();";
			String toNode = e.to().getAttr(XCSG.name).toString().split("\\(")[0];
			toNode += "();";
			
			if (!staticCFG.containsKey(fromFunctionNode)) {
				fromFunctionNode = eFrom.getAttr(XCSG.name).toString();
			}
			
			if (!staticCFG.containsKey(toNode)) {
				toNode = eTo.getAttr(XCSG.name).toString();
			}
			
			if (staticCFG.containsKey(toNode)) {
				Node fromCheck = recreatedNodes.get(e.from());
				if (fromCheck == null) {
					fromCheck = createNode(e.from(), false, functionNode);
					recreatedNodes.put(e.from(), fromCheck);
					
					fromCheck.tag("static_transform");
					Edge tempEdge = Graph.U.createEdge(functionNode, fromCheck);
					tempEdge.tag(XCSG.Contains);
				}
				
				Node successor = e.to().out(XCSG.ControlFlow_Edge).one().to();
				Node toCheck = recreatedNodes.get(successor);
				if (toCheck == null) {
					toCheck = createNode(successor, false, functionNode);
					recreatedNodes.put(successor, toCheck);
					
					toCheck.tag("static_transform");
					Edge tempToEdge = Graph.U.createEdge(functionNode, toCheck);
					tempToEdge.tag(XCSG.Contains);
				}
				
				Q sFunction = staticCFG.get(toNode);
				System.out.println(sFunction.eval().edges().size());
				//Check to make sure we haven't already made the static CFG
				Edge checkEdge = sFunction.eval().edges().tagged(XCSG.ControlFlow_Edge).getFirst();
				Node graphCheck = recreatedNodes.get(checkEdge.from());
				if (graphCheck != null) {
					//If graph has already been made, just add edges from predecessor to root
					Node r = sFunction.roots().eval().nodes().one();
					Node root = recreatedNodes.get(r);
					createEdge(e, e.from(), root);
					continue;
				}
				
				for(Edge eStatic : sFunction.eval().edges()) {
					Node from = recreatedNodes.get(eStatic.from());
					Node to = recreatedNodes.get(eStatic.to());
					
					if (from == null) {
						 from = createNode(eStatic.from(), true, functionNode);
						 recreatedNodes.put(eStatic.from(), from);
					}
					if (to == null) {
						to = createNode(eStatic.to(), true, functionNode);
						recreatedNodes.put(eStatic.to(), to);

					}
				
					createEdge(eStatic, from, to);					
				}
				
//				recreatedNodes.put(e.to(), e.to());
				Node r = sFunction.roots().eval().nodes().one();
				Node root = recreatedNodes.get(r);
				createEdge(e, e.from(), root);
				
				for (Node l : sFunction.leaves().eval().nodes()) {
					Node createdLeaf = recreatedNodes.get(l);
					createEdge(e.to().out(XCSG.ControlFlow_Edge).one(), createdLeaf, toCheck);
				}
				
				
			}
			else if (staticCFG.containsKey(fromFunctionNode)) {
				
				//Check to see if we've already created the static CFG
				if (recreatedNodes.containsKey(e.from())) {
					//If graph has already been made, just add edges to from leaves to successor
					String fromName = e.from().getAttr(XCSG.name).toString();
					Q sCFG = staticCFG.get(fromName);
					for (Node l : sCFG.leaves().eval().nodes()) {
						Node createdLeaf = recreatedNodes.get(l);
						createEdge(e, createdLeaf, e.to());
					}
					continue;
				}
				
				Node successor = e.to();
				Node toCheck = recreatedNodes.get(successor);
				
				if (toCheck == null) {
					toCheck = createNode(e.to(), false, functionNode);
					recreatedNodes.put(e.to(), toCheck);
					
					toCheck.tag("static_transform");
					Edge tempEdge = Graph.U.createEdge(functionNode, toCheck);
					tempEdge.tag(XCSG.Contains);
				}
				
				Q sFunction = staticCFG.get(fromFunctionNode);
				for(Edge eStatic : sFunction.eval().edges()) {
					Node from = recreatedNodes.get(eStatic.from());
					Node to = recreatedNodes.get(eStatic.to());
					
					if (from == null) {
						 from = createNode(eStatic.from(), true, functionNode);
						 recreatedNodes.put(eStatic.from(), from);
					}
					if (to == null) {
						to = createNode(eStatic.to(), true, functionNode);
						recreatedNodes.put(eStatic.to(), to);

					}
				
					createEdge(eStatic, from, to);
				}
				
				for (Node l : sFunction.leaves().eval().nodes()) {
					Node createdLeaf = recreatedNodes.get(l);
					createEdge(e, createdLeaf, toCheck);
				}

			}
			else {
				Node from = createNode(e.from(), false, functionNode);
				Node to = createNode(e.to(), false, functionNode);
				
				Node fromCheck = recreatedNodes.get(e.from());
				Node toCheck = recreatedNodes.get(e.to());
				
				if (fromCheck == null && toCheck == null) {
					recreatedNodes.put(e.from(), from);
					recreatedNodes.put(e.to(), to);	
					createEdge(e, from, to);
					
					
					from.tag("static_transform");
					Edge fromEdge = Graph.U.createEdge(functionNode, from);
					fromEdge.tag(XCSG.Contains);
					
					
					to.tag("static_transform");
					Edge toEdge = Graph.U.createEdge(functionNode, to);
					toEdge.tag(XCSG.Contains);
				}
				else if (fromCheck != null && toCheck == null) {
					recreatedNodes.put(e.to(), to);	
					createEdge(e, fromCheck, to);
					
					to.tag("static_transform");
					Edge toEdge = Graph.U.createEdge(functionNode, to);
					toEdge.tag(XCSG.Contains);
				}
				else if (fromCheck == null && toCheck != null) {
					recreatedNodes.put(e.from(), from);	
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
	
	private static class staticHeaderNode{
		private Node staticHeader;
		private Node toNode;
		private Node createdNode;
		private Node fromNode;
		
		public staticHeaderNode(Node n, Node f, Node t) {
			this.staticHeader = n;
			this.fromNode = f;
			this.toNode = t;
		}
		
		public Node getToNode() {
			return this.toNode;
		}
//		
//		public Node getOriginalNode() {
//			return this.originalNode;
//		}
		
//		public long getLineNumber() {
//			return this.lineNumber;
//		}
		
		public void setCreatedNode(Node n) {
			this.createdNode = n;
		}
		
//		public void setSwitchNode(Node n) {
//			this.switchNode = n;
//		}
	
	}
	
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

}
