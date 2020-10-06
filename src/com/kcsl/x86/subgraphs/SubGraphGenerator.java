package com.kcsl.x86.subgraphs;

import static com.kcsl.x86.Importer.*;

import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

/**
 * 
 * @author RyanGoluch
 *
 */

public class SubGraphGenerator {
	
	/**
	 * 
	 */

	public static Q findSubGraph(String name) {
		
		//Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		Q f = my_function(name);	
		Q c = my_cfg(f);
		
		//Get all the nodes tagged with control flow conditions that would cause some form
		//of branching in the graph
		Q if_nodes = c.nodesTaggedWithAll(XCSG.ControlFlowIfCondition);
		Q loop_nodes = c.nodesTaggedWithAll(XCSG.ControlFlowLoopCondition);
		Q switch_nodes = c.nodesTaggedWithAll(XCSG.ControlFlowSwitchCondition);
		
		//Find and generate the sub graph that is bounded above by if statements
		Q if_and_loops = Query.universe().edges(XCSG.ControlFlow_Edge).between(if_nodes, loop_nodes);
		Q if_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(if_nodes, switch_nodes);
		Q if_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(if_nodes, if_nodes);
		
		Q if_subgraph = if_and_loops.union(if_and_switch).union(if_and_if);
		
		
		//Find and generate the subgraph that is bounded above by loop conditions
		Q loops_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(loop_nodes, if_nodes);
		Q loops_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(loop_nodes, switch_nodes);
		Q loops_and_loops = Query.universe().edges(XCSG.ControlFlow_Edge).between(loop_nodes, loop_nodes);
		
		Q loop_subgraph = loops_and_if.union(loops_and_switch).union(loops_and_loops);
		
		
		//Find and generate the subgraph that is bounded above by switch statements
		Q switch_and_if = Query.universe().edges(XCSG.ControlFlow_Edge).between(switch_nodes, if_nodes);
		Q switch_and_loop = Query.universe().edges(XCSG.ControlFlow_Edge).between(switch_nodes, loop_nodes);
		Q switch_and_switch = Query.universe().edges(XCSG.ControlFlow_Edge).between(switch_nodes, switch_nodes);
		
		
		//TODO Fix the unions to not add any extraneous edges
		Q switch_subgraph = switch_and_if.union(switch_and_loop).union(switch_and_switch);
		
		Q subgraph = if_subgraph.union(loop_subgraph).union(switch_subgraph);
		
		return subgraph;
	}
	
	public static void findAllSourceSubGraphs() {
		
	}
	
	public static void findAllBinarySubGraphs() {
		
	}
	
	public static void findAllSubGraphs() {
		
	}
	
}
