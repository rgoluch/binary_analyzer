package com.kcsl.x86.support;

import static com.kcsl.x86.Importer.loop_tagging;
import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;
import com.se421.paths.transforms.DAGTransform;

import java.io.File;
import java.util.ArrayList;
import java.util.Map;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
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
			AtlasSet<Edge> edges = n.out();
			if((edges.size() == 2 || n.taggedWith(XCSG.ControlFlowIfCondition)) && !n.taggedWith(XCSG.ControlFlowLoopCondition)) {
				n.tag(XCSG.ControlFlowIfCondition);
			}
		}
		
	}
	
	public static void tag_binary_branches(String name) {
		Q function = my_function(name);
		Q cfg = my_cfg(function);
		
		for (Node n : cfg.eval().nodes()) {
			AtlasSet<Edge> edges = n.out();
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
			r = Common.toQ(g).nodes("self_loop");
			//DisplayUtil.displayGraph(c);
		}
		
		if(CommonQueries.isEmpty(r)) {

		}
		else {
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
				n.tag(XCSG.ControlFlowLoopCondition);
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
		}
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
	
	public static Q staticCFGFinder(String name, String staticFunction) {
		Q f = Query.universe().nodes(XCSG.C.TranslationUnit);
		Q found = f.selectNode(XCSG.name, name);
		Q c = found.children().selectNode(XCSG.name, staticFunction);
		Q graph = c.contained().nodes(XCSG.ControlFlow_Node).induce(Query.universe().edges(XCSG.ControlFlow_Edge));
		
		return graph;
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
		Q staticNames = found.children().nodes(XCSG.C.Provisional.internalLinkage);
		AtlasSet<Node> callNodes = found.contained().eval().nodes().taggedWithAll(XCSG.DataFlow_Node, XCSG.SimpleCallSite);
		
		AtlasSet<Node> functionNodes = staticNames.eval().nodes();
		ArrayList<String> functionNames = new ArrayList<String>();
		for (Node f1 : functionNodes) {
			functionNames.add(f1.getAttr(XCSG.name).toString());
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
	
//	public static Edge createEdge(Edge e, Node f, Node t, String[] transformTags) {
//		Edge cfgEdge = Graph.U.createEdge(f, t);
//		cfgEdge.tag(XCSG.ControlFlow_Edge);
//		for (String s : transformTags) {
//			cfgEdge.tag(s);
//		}
//		
//		if (e.hasAttr(XCSG.conditionValue)) {
//			String conditionVal = e.getAttr(XCSG.conditionValue).toString();
//			cfgEdge.putAttr(XCSG.conditionValue, conditionVal);
//			if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
//				cfgEdge.putAttr(XCSG.name, "true");
//			}else if (e.getAttr(XCSG.conditionValue).toString().contains("false")){
//				cfgEdge.putAttr(XCSG.name, "false");
//			}else if (e.getAttr(XCSG.conditionValue).toString().contains("default")) {
//				cfgEdge.putAttr(XCSG.name, "default");
//			}
//		}
//		
//		if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
//			cfgEdge.tag(XCSG.ControlFlowBackEdge);
//		}
//		
//		return cfgEdge;
//	}
	
}
