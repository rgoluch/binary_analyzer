package com.kcsl.x86;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Scanner;
import static com.kcsl.x86.Importer.*;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.GraphElement;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.open.commons.algorithms.LoopIdentification;
import com.se421.paths.algorithms.PathCounter.CountingResult;
import com.se421.paths.algorithms.counting.MultiplicitiesPathCounter;

public class Verifier {
	
	/**
	 * Determines the number of function exits that exist in
	 * the disassembled binary based on the number of nodes
	 * that have an out degree of 0. If the number of outgoing
	 * edges is 0, then you know you have a leaf of the CFG.
	 * 
	 * @param name
	 * 		Name of the function that you want to count the exits of
	 * @return
	 * 		The number of exit points in the function
	 */
	
	public static long count_exits(String name) {
		Q function = my_function(name);
		Q cfg = my_cfg(function);
		AtlasSet<Node> leaves = cfg.eval().nodes();
		
		long incoming = 0; 
		for(Node n : leaves) {
			if(n.out().size() == 0) {
				incoming += 1;
			}
		}
		return incoming;
	}
	
	
	/**
	 * TODO
	 */
	
	public static void count_loops(String name) {
		Q function = my_function(name);
		Q cfg = my_cfg(function);
		
		
	}
	
	
	/**
	 * Determines the number of conditional statements in binary based
	 * on the number of outgoing edges from each control flow node. 
	 * If the number of outgoing edges is > 1, then you know you have a 
	 * branching condition. 
	 * 
	 * @param name
	 * 		Name of the function that you want to count the conditionals of
	 * @return
	 * 		The number of conditional statements in the given binary CFG
	 */
	
	public static long count_conditionals(String name) {
		Q function = my_function(name);
		Q cfg = my_cfg(function);
		
		long count = 0;
		
		for (Node n : cfg.eval().nodes()) {
			if(n.out().size() > 1) {
				count +=1;
			}
		}
		
		return count;
	}
	
	
	/**
	 * TODO
	 */
	
	public static void verify_all_counts(String name){
//		Q function = my_function(name);
//		Q cfg = my_cfg(function);
		
		long exits = count_exits(name);
	}
	
	
	/**
	 * TODO
	 */
	
	public static void verify_all_graphs() {
		
	}
}
