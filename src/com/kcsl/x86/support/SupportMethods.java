package com.kcsl.x86.support;

import static com.kcsl.x86.Importer.loop_tagging;
import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;
import static com.kcsl.x86.support.SupportMethods.srcTransformedGraph;

import com.se421.paths.transforms.DAGTransform;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.index.common.SourceCorrespondence;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.script.CommonQueries;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.ui.viewer.graph.SaveUtil;
import com.ensoftcorp.open.commons.algorithms.LoopIdentification;

/**
 * 
 * @author RyanGoluch
 *
 */

public class SupportMethods {
	
	/**
	 * 
	 * @param name
	 */
	
	public static void tag_binary_ifs(String name) {
		Q function = my_function(name);
		Q cfg = my_cfg(function);
		
		for (Node n : cfg.eval().nodes()) {
			AtlasSet<Edge> edges = n.out(XCSG.ControlFlow_Edge);
			if((edges.size() == 2 || n.taggedWith(XCSG.ControlFlowIfCondition)) && !n.taggedWith(XCSG.ControlFlowLoopCondition)) {
				n.tag(XCSG.ControlFlowIfCondition);
			}
		}
		
	}
	
	public static void tag_binary_branches(String name) {
		Q function = my_function(name);
		Q cfg = my_cfg(function);
		
		for (Node n : cfg.eval().nodes()) {
			AtlasSet<Edge> edges = n.out(XCSG.ControlFlow_Edge);
			if(edges.size() == 2) {
				n.tag(XCSG.ControlFlowCondition);
			}
		}
		
	}
	
	
	/**
	 * 
	 * @param name
	 */
	
	public static void tag_binary_exits(String name) {
		Q function = my_function(name);
		Q cfg = my_cfg(function);
		
		for (Node n : cfg.eval().nodes()) {
			AtlasSet<Edge> edges = n.out();
			if(edges.size() == 0) {
				n.tag(XCSG.controlFlowExitPoint);
			}
		}
		
	}
	
	
	public static void tag_binary_single_exits(String name) {
		Q function = my_function(name);
		Q cfg = my_cfg(function);
		
		Node exit = cfg.eval().nodes().tagged(XCSG.controlFlowExitPoint).getFirst();
		
		for (Node n : cfg.eval().nodes()) {
			AtlasSet<Edge> edges = n.out();
			if(edges.size() == 0 && !n.taggedWith("single_exit")) {
				Edge temp = Graph.U.createEdge(n, exit);
				temp.tag("my_edge");
				temp.tag(XCSG.ControlFlow_Edge);
			}
		}
	}
	
	
	
	/**
	 * 
	 * @param name
	 */
	
	public static void  tag_binary_loops(String name) {
		Q function = my_function(name);
		Graph cfg = my_cfg(function).eval();
		loop_tagging(cfg, name);
	}
	
	
	/**
	 * Method to go through the given Atlas graph and function name
	 * and identify and properly tag the loop nodes as well as the 
	 * loop back edge
	 * 
	 * @param g
	 * 		The Atlas graph object to go through and identify
	 * @param name
	 * 		Name of the function graph being passed in
	 */
	
	public static void loop_tagging(Graph g, String name) {
		
		Q r = Common.toQ(g).roots();
		if(CommonQueries.isEmpty(r)) {
			System.out.println(name);
			r = Common.toQ(g.nodes().tagged(XCSG.controlFlowRoot).one());
//					Common.toQ(g).nodes("self_loop");
			//DisplayUtil.displayGraph(c);
		}
		
//		if(CommonQueries.isEmpty(r)) {
//
//		}
//		else {
		
//			for(Node n : g.nodes().tagged(XCSG.controlFlowRoot)) {
//				System.out.println(n);
//			}
		
			Node checking = r.eval().nodes().one();
			LoopIdentification l = new LoopIdentification(g, r.eval().nodes().one());
			AtlasSet<Edge> back = l.getLoopbacks();
			Map<Node,Node> loopNodes = l.getInnermostLoopHeaders();
			ArrayList<Node> headers = new ArrayList<Node>();
			
			for (Node n : l.getInnermostLoopHeaders().values()) {
				if (!headers.contains(n)) {
					headers.add(n);
				}
			}
			
			for (Node n : headers) {
				if (n.out(XCSG.ControlFlow_Edge).size() == 2) {
					n.tag(XCSG.ControlFlowLoopCondition);
				}else if (n.out(XCSG.ControlFlow_Edge).size() < 2 && n.taggedWith(XCSG.ControlFlowCondition)) {
					n.untag(XCSG.ControlFlowCondition);
				}
				
			}
			
			for (Edge e : back) {
				e.tag(XCSG.ControlFlowBackEdge);
				e.from().tag("bin_loopback_tail");
			}
			
			for (Node n : loopNodes.values()) {
				n.tag(XCSG.Loop);
			}
			
			for (Node n : loopNodes.keySet()) {
				n.tag(XCSG.Loop);
			}
//		}
	}
	
	
	/**
	 * 
	 */
	
	public static void binaryCountExporter() {
		
	}
	
	
	public static Q subGraphGenerator(String name) {
		
		Q f = my_function(name);	
		Q c = my_cfg(f);
//		DAGTransform d = new DAGTransform();
		
		
		//Get all the nodes tagged with control flow conditions that would cause some form
		//of branching in the graph
		Q ifNodes = c.nodesTaggedWithAll(XCSG.ControlFlowIfCondition);		
		Q loopNodes = c.nodesTaggedWithAll(XCSG.ControlFlowLoopCondition);
		Q switchNodes = c.nodesTaggedWithAll(XCSG.ControlFlowSwitchCondition);
		Q exitNodes = c.nodesTaggedWithAll(XCSG.controlFlowExitPoint);
		
		//Find and generate the sub graph that is bounded above by if statements
		Q if_and_loops = Query.universe().edges(XCSG.ControlFlow_Edge).between(ifNodes, exitNodes);
		Q if_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(ifNodes, exitNodes);
		Q if_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(ifNodes, exitNodes);
		
		Q if_subgraph = if_and_loops.union(if_and_switch).union(if_and_if);
		
		//Find and generate the subgraph that is bounded above by loop conditions
		Q loops_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(loopNodes, exitNodes);
		Q loops_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(loopNodes, exitNodes);
		Q loops_and_loops = Query.universe().edges(XCSG.ControlFlow_Edge).between(loopNodes, exitNodes);
		
		Q loop_subgraph = loops_and_if.union(loops_and_switch).union(loops_and_loops);
		
		//Find and generate the subgraph that is bounded above by switch statements
		Q switch_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(switchNodes, exitNodes);
		Q switch_and_loop = Query.universe().edges(XCSG.ControlFlow_Edge).between(switchNodes, exitNodes);
		Q switch_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(switchNodes, exitNodes);
		
		Q switch_subgraph = switch_and_if.union(switch_and_loop).union(switch_and_switch);
		
		Q subgraph = if_subgraph.union(loop_subgraph).union(switch_subgraph);
//		Q dag = d.transform(subgraph);
		return subgraph;
//		return dag;
	}
	
	/**
	 * 
	 * @param name
	 * @return
	 */
	
	public static Q bcfg(String name) {
		Q f = my_function(name);
		Q c = my_cfg(f);
		
		return c;
	}
	
	public static Q srcTransformedGraph(String name) {
		Q f = Query.universe().nodes(XCSG.Function);
		Q found = f.selectNode(XCSG.name, "isomorphic_checking_"+name);
		Q c = found.contained().nodes("src_node").induce(Query.universe().edges("src_induced_edge"));
		
		return c;
	}
	
	public static Q binTransformedGraph(String name) {
		Q f = Query.universe().nodes(XCSG.Function);
		Q found = f.selectNode(XCSG.name, name);
		Q c = found.contained().nodes("bin_node").induce(Query.universe().edges("bin_induced_edge"));
		
		return c;
	}
	
	
	public static Q staticCFGFinder(String name, String staticFunction) {
		Q f = Query.universe().nodes(XCSG.C.TranslationUnit);
		Q found = f.selectNode(XCSG.name, name);
		Q c = found.children().selectNode(XCSG.name, staticFunction);
		Q graph = c.contained().nodes(XCSG.ControlFlow_Node).induce(Query.universe().edges(XCSG.ControlFlow_Edge));
		
		return graph;
	}
	
	public static Q getReversedGraph(String name) {
		Q f = Query.universe().nodes(XCSG.Function);
		Q found = f.selectNode(XCSG.name, "reversed_"+name);
		Q c = found.contained().nodes("reversed_graph").induce(Query.universe().edges("reversed_edge"));
		
		return c;
	}
	
	public static Q getFailPoint(Node t, String functionName, int mode) {
		Node srcForward = t;		
		String srcFName = srcForward.getAttr(XCSG.name).toString().split("LABEL:")[0];
		srcFName = srcFName.replaceAll("\\n", "");
		
		Q transformed = null;
		if (mode == 0) {
			transformed = srcTransformedGraph(functionName);
		}else {
			transformed = binTransformedGraph(functionName);
		}
		Node sFwd = null;
		for (Node n : transformed.eval().nodes()) {
			String nName = n.getAttr(XCSG.name).toString();
			if (nName.contains(srcFName)) {
				sFwd = n;
				break;
			}
		}
		
		Q fwdQ = Common.toQ(sFwd);
		return fwdQ;
	}
	
	/**
	 * 
	 * @param f
	 * @return
	 */
	
	public static ArrayList<Node> my_dataFlow(String name) {
		name = name +".c";
		Q f = Query.universe().nodes(XCSG.C.TranslationUnit);
		Q found = f.selectNode(XCSG.name, name);
		Q foundEdges = found.edges(XCSG.Call);
		Q staticNames = found.induce(foundEdges).nodes(XCSG.C.Provisional.internalLinkage, XCSG.Function);
		AtlasSet<Node> staticNames2 = found.children().eval().nodes().taggedWithAll(XCSG.C.Provisional.internalLinkage, XCSG.Function);
//		long size = staticNames2.size();
//		long size2 = staticNames.eval().nodes().size();
//				.children().eval().nodes().taggedWithAll(XCSG.C.Provisional.internalLinkage, XCSG.Function);
		AtlasSet<Node> callNodes = found.contained().eval().nodes().taggedWithAll(XCSG.DataFlow_Node, XCSG.SimpleCallSite);
		AtlasSet<Node> functionNodes = staticNames.eval().nodes();
		

		ArrayList<String> functionNames = new ArrayList<String>();
		for (Node f1 : functionNodes) {
			functionNames.add(f1.getAttr(XCSG.name).toString());
		}
		for (Node s1 : staticNames2) {
			functionNames.add(s1.getAttr(XCSG.name).toString());
		}

		ArrayList<Node> foundNodes = new ArrayList<Node>();
		for(Node c : callNodes) {
			String s = c.getAttr(XCSG.name).toString().split("\\(")[0];
			if (functionNames.contains(s) && !foundNodes.contains(c)) {
				foundNodes.add(c);
			}
		}
		
		return foundNodes;
	}
	
	public static Node createNode(Node original, String[] transformTags) {
		Node returnNode = null;
		
		Iterable<String> tags = original.tagsI();
		returnNode = Graph.U.createNode();
		returnNode.putAllAttr(original.attr());
		String name = original.getAttr(XCSG.name).toString();
		returnNode.putAttr(XCSG.name, name);
		
		for (String s : tags) {
			returnNode.tag(s);
		}
		
		for (String t : transformTags) {
			returnNode.tag(t);
		}
		
		return returnNode;
	}
	
	public static Q createReverseGraph(Q originalGraph, String originalName, int flag) {
		Node originalRoot = originalGraph.eval().nodes().tagged(XCSG.controlFlowRoot).one();
		Node originalExit = originalGraph.eval().nodes().tagged("single_exit").getFirst();
		
		String tag = null;
		String edgeTag = null;
		if (flag == 1) {
			tag = "bin_node";
			edgeTag = "bin_induced_edge";
		}else {
			tag = "src_node";
			edgeTag = "src_induced_edge";
		}
		
		Map<Node, Node> recreatedNodes = new HashMap<Node, Node>();
		
		Node newFunc = Graph.U.createNode();
		newFunc.putAttr(XCSG.name, "reversed_"+originalName);
		newFunc.tag(XCSG.Function);
		
		for (Node n : originalGraph.eval().nodes().tagged(tag)) {
			for (Edge e : n.out().tagged(edgeTag)) {
				Node from = e.from();
				Node to = e.to();
				Node newFrom = null;
				Node newTo = null;
				
				if (recreatedNodes.get(to) == null) {
					newFrom = Graph.U.createNode();
					newFrom.tag("reversed_graph");
					Iterable<String> i = e.to().tagsI();
					
					for (String s : i) {
						newFrom.tag(s);
					}
					newFrom.putAllAttr(e.to().attr());
					Edge e1 = Graph.U.createEdge(newFunc, newFrom);
					e1.tag(XCSG.Contains);
					
					recreatedNodes.put(to, newFrom);
				}else {
					newFrom = recreatedNodes.get(to);
				}
				
				if (recreatedNodes.get(from) == null) {
					newTo = Graph.U.createNode();
					newTo.tag("reversed_graph");
					Iterable<String> i = e.from().tagsI();
					
					for (String s : i) {
						newTo.tag(s);
					}
					newTo.putAllAttr(e.from().attr());
					Edge e2 = Graph.U.createEdge(newFunc, newTo);
					e2.tag(XCSG.Contains);
					
					recreatedNodes.put(from, newTo);
				}else {
					newTo = recreatedNodes.get(from);
				}
				
				
				Edge e3 = Graph.U.createEdge(newFrom, newTo);
				Iterable<String> i = e.tagsI();
				for (String s : i) {
					e3.tag(s);
				}
				e3.tag("reversed_edge");
				e3.putAllAttr(e.attr());
			}
		}
		
		Node newRoot = recreatedNodes.get(originalRoot);
		newRoot.untag(XCSG.controlFlowRoot);
		newRoot.tag(XCSG.controlFlowExitPoint);
		newRoot.tag("single_exit");
		if (flag == 1) {
			newRoot.tag("bin_exit");
		}else {
			newRoot.tag("src_exit");
		}
		
		Node newExit = recreatedNodes.get(originalExit);
		newExit.tag(XCSG.controlFlowRoot);
		newExit.untag(XCSG.controlFlowExitPoint);
		newExit.untag("single_exit");
		if (flag == 1) {
			newExit.untag("bin_exit");
		}else {
			newExit.untag("src_exit");
		}
		
		Q x = my_function(newFunc.getAttr(XCSG.name).toString());
		Q reversedGraph = x.contained().nodes("reversed_graph").induce(Query.universe().edges("reversed_edge"));
		
		return reversedGraph;
	}
	
	
	public static Long getCSourceLineNumber(Node node) {
		long lineNumber = -1;
		if (node.hasAttr(XCSG.sourceCorrespondence)) {
			SourceCorrespondence sc = (SourceCorrespondence) node.getAttr(XCSG.sourceCorrespondence);
			if (sc != null) {
				lineNumber = sc.startLine;
			}
		}
		return lineNumber;
	}
	
}
