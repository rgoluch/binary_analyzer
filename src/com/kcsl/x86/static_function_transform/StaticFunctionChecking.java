package com.kcsl.x86.static_function_transform;

import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;
import static com.kcsl.x86.support.SupportMethods.*;

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;

import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
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
//		;
		Q cfg = my_cfg(f);
		Q dfg = my_dataFlow(f);
		
		ArrayList<String> staticFunctions = staticChecker();
		ArrayList<Node> callSites = new ArrayList<Node>();
		
		for (Node x : dfg.eval().nodes()) {
			if (x.taggedWith(XCSG.Function)) {
				callSites.add(x);
			}
		}
		
		int count = 0; 
		
		for (Node y : callSites) {
			if (staticFunctions.contains(y.getAttr(XCSG.name))) {
				count++;
			}
		}
		
		System.out.println(callSites);
		
		
		return f.edges(XCSG.Call);
		
	}

}
