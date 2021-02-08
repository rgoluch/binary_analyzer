package com.kcsl.x86.isomorphism;

import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

import static com.kcsl.x86.static_function_transform.StaticFunctionChecking.*;
import static com.kcsl.x86.switch_transform.SwitchStatementChecking.*;
import static com.kcsl.x86.subgraphs.SubGraphGenerator.*;

public class IsomorphismChecking {
	
	public static Q createSrcGraph(String functionName) {
		
		Q staticSrcGraph = staticTransform(functionName);
		Q switchSrcGraph = switchTransform(functionName, staticSrcGraph);
		String name = switchSrcGraph.containers().nodes(XCSG.Function).eval().nodes().one().getAttr(XCSG.name).toString();
		Q scSrcGraph = singleSrcReturn(switchSrcGraph, name);
		Q srcSubGraph = findSrcSubGraph(scSrcGraph);
		
		return srcSubGraph;
	}
}
