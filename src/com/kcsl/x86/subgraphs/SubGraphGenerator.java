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

	public static Q findSubGraphs(String name) {
		
		//Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		Q f = my_function(name);
//		Q f_binary = my_function("sym_kill");
		
		Q c = my_cfg(f);
//		Q c_binary = my_cfg(f_binary);
		
		Q nodes = c.nodesTaggedWithAll(XCSG.ControlFlowIfCondition);
		Q exits = c.nodesTaggedWithAll(XCSG.ControlFlow_Node);
		return Query.universe().edges(XCSG.ControlFlow_Edge).between(nodes, nodes);
	}
	
}
