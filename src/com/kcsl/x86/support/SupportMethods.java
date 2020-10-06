package com.kcsl.x86.support;

import static com.kcsl.x86.Importer.loop_tagging;
import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;

import java.io.File;
import java.util.Map;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.script.CommonQueries;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.ui.viewer.graph.SaveUtil;
import com.ensoftcorp.open.commons.algorithms.LoopIdentification;

public class SupportMethods {
	
	public static void tag_binary_conditionals(String name) {
		Q function = my_function(name);
		Q cfg = my_cfg(function);
		
		for (Node n : cfg.eval().nodes()) {
			AtlasSet<Edge> edges = n.out();
			if((edges.size() == 2 || n.taggedWith(XCSG.ControlFlowIfCondition)) && !n.taggedWith(XCSG.ControlFlowLoopCondition)) {
//				 && !edges.one().taggedWith(XCSG.ControlFlowBackEdge)
				n.tag(XCSG.ControlFlowIfCondition);
			}
		}
		
	}
	
	
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
			SaveUtil.saveGraph(new File("/Users/RyanGoluch/Desktop/cfg_"+name+".png"), g);
		}
		else {

			LoopIdentification l = new LoopIdentification(g, r.eval().nodes().one());
			Map<Node,Node> loopNodes = l.getInnermostLoopHeaders();
			for (Node n : loopNodes.values()) {
				n.tag(XCSG.Loop);
			}
			
			for (Node n : loopNodes.keySet()) {
				n.tag(XCSG.Loop);
			}
		
			for (Node n : g.nodes()) {
				AtlasSet<Edge> outEdges = n.out();
				for (Edge e : outEdges) {
					if (((e.to().taggedWith(XCSG.Loop) && !e.from().taggedWith(XCSG.Loop)) || e.from().taggedWith(XCSG.DoWhileLoop)) && !n.taggedWith(XCSG.Loop) && !e.to().taggedWith(XCSG.ControlFlowIfCondition)) {
						e.to().tag(XCSG.ControlFlowLoopCondition);
					}
				}
			}
			
			for (Edge e : g.edges()) {
				if (e.from().taggedWith(XCSG.Loop) && e.to().taggedWith(XCSG.ControlFlowLoopCondition)) {
					e.tag(XCSG.ControlFlowBackEdge);
				}
			}
		}
	}
	
}
