package com.kcsl.x86.ternary_ops;

import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

public class TernaryOperatorChecking {
	
	public static int ternaryOpChecker(Q cfg) {
		
		AtlasSet<Node> cfNodes = cfg.eval().nodes().tagged(XCSG.ControlFlow_Node);
		
		int terCount = 0; 
		
		for (Node n : cfNodes) {
			
			if (Common.toQ(n).contained().nodes(XCSG.TernaryCondition).eval().nodes().size() > 0) {
//				System.out.println(n.getAttr(XCSG.name).toString());
//				System.out.println(n.getAttr(XCSG.name).toString().split("?")[0]);
//				System.out.println(n.getAttr(XCSG.name).toString().split("?")[1]);
				terCount++;
			}
		}
		
		return terCount;
	}
	
	
	public static void ternaryOpCounter() throws IOException {
		
		String topPath = "/Users/RyanGoluch/Desktop/Masters_Work/isomorphism_checking/ternary_op_checking.csv";
		File topFile = new File(topPath);
		BufferedWriter topWriter = new BufferedWriter(new FileWriter(topFile));
		topWriter.write("Function Name, # of Ternary Ops\n");
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		
		for (Node f : functions.eval().nodes()) {
			String functionName = f.getAttr(XCSG.name).toString();
			String srcName = functionName.substring(4);
			
			if (functionName.contains("test")) {
				continue;
			}
			
			Q function = my_function(srcName);
			Q c = my_cfg(function);
			
			int result = ternaryOpChecker(c);
			
			if (result > 0) {
				topWriter.write(srcName + "," + result + "\n");
				topWriter.flush();
			}
		}
		topWriter.close();
	}
}
