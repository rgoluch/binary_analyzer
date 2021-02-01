package com.kcsl.x86.static_function_transform;

import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;
import static com.kcsl.x86.support.SupportMethods.*;

import java.util.ArrayList;

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
	
	public static ArrayList<String> staticChecker() {
			
		ArrayList<String> staticFunctions = new ArrayList<String>();
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.C.Provisional.internalLinkage);
//		int staticCount = 0;
		for (Node f : functions.eval().nodes()) {
			String functionName = f.getAttr(XCSG.name).toString();
			
//			Q function = my_function(functionName);
//			for (Node n : function.eval().nodes()) {
//				if (f.taggedWith(XCSG.StaticDispatchCallSite)) {
//					staticCount++;
					if (!staticFunctions.contains(functionName)) {
						staticFunctions.add(functionName);
					}
//				}
//			}
		}		
		return staticFunctions;
	}
	
	public static Q staticTransform(String functionName) {
		
		Q f = my_function(functionName);
		Q cfg = my_cfg(f);
		Q dfg = my_dataFlow(functionName);
		
		ArrayList<String> staticFunctions = staticChecker();
		ArrayList<Node> callSites = new ArrayList<Node>();
		int count = 0; 
		
		for (Node y : dfg.eval().nodes()) {
			if (staticFunctions.contains(y.getAttr(XCSG.name))) {
				count++;
				callSites.add(y);
			}
		}
		
		ArrayList<Q> staticCFG = new ArrayList<Q>();
		for (Node c : callSites) {
			Q b = bcfg(c.getAttr(XCSG.name).toString());
			String bTU = b.nodes(XCSG.C.TranslationUnit).toString();
			String dTU = cfg.nodes(XCSG.C.TranslationUnit).toString();
			System.out.println(dTU);
//			if (b.containers().)
			staticCFG.add(b);
		}
		
		Node functionNode = Graph.U.createNode();
		functionNode.putAttr(XCSG.name, "static_transform_"+functionName);
		functionNode.tag(XCSG.Function);

		for (Q b : staticCFG) {
//			Node bFunction = b.eval().edges().tagged(XCSG.Contains).getFirst().from();
			for (Node d : b.eval().nodes()) {
				d.tag("static_node");
				Edge e = Graph.U.createEdge(functionNode, d);
				e.tag(XCSG.Contains);
			}
		}
		
		
		System.out.println(count);
		
		
		Q x = my_function(functionNode.getAttr(XCSG.name).toString());
		Q static_cfg = my_cfg(x);
		return static_cfg.nodes("static_node");
		
	}

}
