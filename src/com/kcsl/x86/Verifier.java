package com.kcsl.x86;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import static com.kcsl.x86.Importer.*;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.xcsg.XCSG;


/**
 * 
 * @author RyanGoluch
 *
 */

public class Verifier {
	
	private static long exits;
	private static long conditionals;
	private static long loops;
	
	/**
	 * Determines the number of function exits that exist in
	 * the disassembled binary based on the number of nodes
	 * that have an out degree of 0. If the number of outgoing
	 * edges is 0, then you know you have a leaf of the CFG.
	 * Adds an additional tag to exit nodes for improved CFG rendering.
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
			if(n.out().size() == 0 || n.taggedWith(XCSG.controlFlowExitPoint)) {
				incoming += 1;
				n.tag(XCSG.controlFlowExitPoint);
			}
		}
		return incoming;
	}
	
	
	/**
	 * Determines the number of loops that exist in the disassembled
	 * binary. Calls the loop_tagging function from Importer.java first
	 * in order to ensure that all loops are tagged and then can count the loops.
	 * 
	 * @param name
	 * 		Name of the function that you want to count loops in
	 * @return
	 * 		The number of loops found in the given function 
	 */
	
	public static long count_loops(String name) {
		Q function = my_function(name);
		Graph cfg = my_cfg(function).eval();
		loop_tagging(cfg, name);
		
		long loopCount = 0;
		for (Node n : cfg.nodes()) {
			if(n.taggedWith(XCSG.ControlFlowLoopCondition)) {
				loopCount++;
			}
		}
		
		return loopCount;
	}
	
	
	/**
	 * Determines the number of conditional statements in binary based
	 * on the number of outgoing edges from each control flow node. 
	 * If the number of outgoing edges is > 1, then you know you have a 
	 * branching condition. Adds an additional tag to the branch nodes for 
	 * improved CFG rendering. 
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
			if(n.out().size() > 1 && !n.taggedWith(XCSG.Loop) && !n.taggedWith(XCSG.ControlFlowLoopCondition)) {
				n.tag(XCSG.ControlFlowIfCondition);
				count +=1;
			}
		}
		
		return count;
	}
	
	
	/**
	 * Counts all of the exits, conditionals, and loops in a given function. 
	 * Then writes those numbers to a CSV on the desktop. 
	 * 
	 * @param name
	 * 		Name of the function to find the counts of
	 * @throws IOException 
	 * 		IOException thrown if the output file path is invalid
	 */
	
	public static void verify_all_counts(String name) throws IOException{

		exits = count_exits(name);
		loops = count_loops(name);
		conditionals = count_conditionals(name);
		
		String verifierPath = "/Users/RyanGoluch/Desktop/count_verifier.csv";
		File verifierFile = new File(verifierPath);
		BufferedWriter verifierWriter = new BufferedWriter(new FileWriter(verifierFile));
		
		verifierWriter.write("Exit_Count, Conditional_Count, Loop_Count\n");
		verifierWriter.write(exits + "," + conditionals + "," + loops);
		verifierWriter.flush();
		
		verifierWriter.close();
	}
	
	
	/**
	 * Counts the exit nodes, conditionals, and loops in all of the functions
	 * that are loaded into Atlas from the disassembled binary and writes the 
	 * results to a CSV on the desktop
	 * 
	 * @throws IOException
	 * 		IOException thrown if the output file path is invalid
	 */
	
	public static void verify_all_graphs() throws IOException {
	 	
		String allCountsPath = "/Users/RyanGoluch/Desktop/all_function_counts.csv";
		File countsFile = new File(allCountsPath);
		BufferedWriter countsWriter = new BufferedWriter(new FileWriter(countsFile)); 
		
		countsWriter.write("Function Name, # Exit Nodes, # Conditionals, # Loops\n");
		countsWriter.flush();
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		
		for(Node function : functions.eval().nodes()) {
			String name = function.getAttr(XCSG.name).toString();
			
			exits = count_exits(name);
			loops = count_loops(name);
			conditionals = count_conditionals(name);
			
			countsWriter.write(name +",");
			countsWriter.write(exits + ", " + conditionals + "," + loops + "\n");
			countsWriter.flush();
		}
		
		countsWriter.close();
	}
}
