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
//				 && !edges.one().taggedWith(XCSG.ControlFlowBackEdge)
				n.tag(XCSG.ControlFlowIfCondition);
//				n.tag(XCSG.ControlFlowCondition);
			}
		}
		
	}
	
	public static void tag_binary_branches(String name) {
		Q function = my_function(name);
		Q cfg = my_cfg(function);
		
		for (Node n : cfg.eval().nodes()) {
			AtlasSet<Edge> edges = n.out();
			if(edges.size() == 2) {
//				|| n.taggedWith(XCSG.ControlFlowIfCondition)) && !n.taggedWith(XCSG.ControlFlowLoopCondition)
//				 && !edges.one().taggedWith(XCSG.ControlFlowBackEdge)
//				n.tag(XCSG.ControlFlowIfCondition);
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
//			Q srcFunction = my_function(name);
//			Q srcCFG = my_cfg(srcFunction);
//			AtlasSet<Node> n = srcCFG.eval().nodes();
//			System.out.println(n.size());
//			GraphElement x = srcCFG.eval().roots().one();
//			System.out.println(x.getAttr(XCSG.name));
//			
//			
//			System.out.println(name+" roots: "+Common.toQ(srcCFG);
//			SaveUtil.saveGraph(new File("/Users/RyanGoluch/Desktop/cfg_"+name+".png"), g);
		}
		else {

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
		
//			for (Node n : g.nodes()) {
//				AtlasSet<Edge> outEdges = n.out();
//				for (Edge e : outEdges) {
//					if (((e.to().taggedWith(XCSG.Loop) && !e.from().taggedWith(XCSG.Loop)) || e.from().taggedWith(XCSG.DoWhileLoop)) 
//							&& !n.taggedWith(XCSG.Loop) && !e.to().taggedWith(XCSG.ControlFlowIfCondition)) {
//						e.to().tag(XCSG.ControlFlowLoopCondition);
////						e.to().tag(XCSG.ControlFlowCondition);
//					}
//				}
//			}
			
//			for (Edge e : g.edges()) {
//				if ((e.from().taggedWith(XCSG.Loop) && e.to().taggedWith(XCSG.ControlFlowLoopCondition)) ||
//						(e.from().taggedWith(XCSG.Loop) && e.to().taggedWith(XCSG.ControlFlowCondition) && e.from().out().size() == 1)){
//					e.tag(XCSG.ControlFlowBackEdge);
//					e.from().tag("bin_loopback_tail");
//					
//					if (!e.to().taggedWith(XCSG.ControlFlowLoopCondition)) {
//						e.to().tag(XCSG.ControlFlowLoopCondition);
//					}
//				}
//			}
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
	
	/**
	 * 
	 * @param f
	 * @return
	 */
	
	public static Q my_dataFlow(Q f) {
		return f.contained().nodes(XCSG.Function).induce(Query.universe().edges(XCSG.Call));
	}
	
}
