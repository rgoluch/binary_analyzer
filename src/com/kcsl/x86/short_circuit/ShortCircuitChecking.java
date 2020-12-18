package com.kcsl.x86.short_circuit;

import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

public class ShortCircuitChecking {
	
	public static scInfo scChecker(Q cfg) {
		
		AtlasSet<Node> conditions = cfg.eval().nodes().tagged(XCSG.ControlFlowCondition);
		ArrayList<String> ordering = new ArrayList<String>();
		scInfo scCount = null;
		
		for (Node n : conditions) {
			AtlasSet<Node> toCheck = Common.toQ(n).contained().nodes(XCSG.LogicalAnd, XCSG.LogicalOr).eval().nodes();
			
			if (toCheck.size() > 0) {
				long and = Common.toQ(n).contained().nodes(XCSG.LogicalAnd).eval().nodes().size();
				long or = Common.toQ(n).contained().nodes(XCSG.LogicalOr).eval().nodes().size();
				scCount = new scInfo(toCheck.size(), and, or);
//				System.out.println("And: " + Common.toQ(n).contained().nodes(XCSG.LogicalAnd).eval().nodes().size());
//				System.out.println("OR: " + Common.toQ(n).contained().nodes(XCSG.LogicalOr).eval().nodes().size());
			}
			
			for (Node x : toCheck) {
				ordering.add(x.getAttr(XCSG.name).toString());
			}
		}
		
//		System.out.println(ordering.toString());
//		System.out.println("Total # Nodes with SC Conditions: " + scCount);
		
		return scCount;
	}
	
	private static class scInfo{
		private long conditions; 
		private long ands;
		private long ors;
		
		public scInfo(long c, long a, long o) {
			this.conditions = c; 
			this.ands = a; 
			this.ors = o;
		}
		
		public long getConditions() {
			return this.conditions;
		}
		
		public long getAnds() {
			return this.ands;
		}
		
		public long getOrs() {
			return this.ors;
		}
	}
	
	public static void scCounts() throws IOException {
		
		String scPath = "/Users/RyanGoluch/Desktop/Masters_Work/isomorphism_checking/sc_checking.csv";
		File scFile = new File(scPath);
		BufferedWriter scWriter = new BufferedWriter(new FileWriter(scFile));
		scWriter.write("Function Name, Conditions, Ands, Ors\n");
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		int result = 0; 
		
		for (Node f : functions.eval().nodes()) {
			String functionName = f.getAttr(XCSG.name).toString();
			String srcName = functionName.substring(4);
			
			if (functionName.contains("test")) {
				continue;
			}
			
			Q function = my_function(srcName);
			Q c = my_cfg(function);
			
			scInfo x = scChecker(c);
			
			if (x != null) {
				result++;
				scWriter.write(srcName + "," + x.getConditions() + "," + x.getAnds() + "," +x.getOrs() + "\n");
				scWriter.flush();
			}
		}
		scWriter.close();
		System.out.println("Number of Source Functions w/ SC: " + result);
		
	}

}
