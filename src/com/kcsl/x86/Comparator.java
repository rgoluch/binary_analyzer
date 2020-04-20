package com.kcsl.x86;

import static com.kcsl.x86.Importer.*;
import static com.kcsl.x86.Verifier.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

/**
 * 
 * @author RyanGoluch
 *
 */

public class Comparator {
	
	/**
	 * Method to count the number of loops identified in a given function 
	 * in both the disassembled binary and the source code.
	 * 
	 * @param name
	 * 		Name of the function to count loops in 
	 * @return 
	 * 		Returns a HashMap of String, Long, with the binary and source
	 * 		loop counts
	 * 
	 */
	
	public static HashMap<String, Long> compare_loops(String name) {
		
		String src_name = name.replace("sym_", "");
		long bin_loops = count_loops(name);
		long src_loops = count_loops(src_name);
		
		HashMap<String, Long> counts = new HashMap<String, Long>();
		counts.put("bin", bin_loops);
		counts.put("src", src_loops);
		
		return counts;
	}
	
	/**
	 * Method to count the number of conditionals in a given function 
	 * in both the disassembled binary and the source code
	 * 
	 * @param name
	 * 		Name of the function to count conditionals in
	 * @return
	 * 		Returns a HashMap of String,Long with the binary and source
	 * 		conditional counts
	 * 
	 */
	
	public static HashMap<String, Long> compare_conditionals(String name) {
		
		String src_name = name.replace("sym_", "");
		long bin_loops = count_conditionals(name);
		long src_loops = count_conditionals(src_name);
		
		HashMap<String, Long> counts = new HashMap<String, Long>();
		counts.put("bin", bin_loops);
		counts.put("src", src_loops);
		
		return counts;
	}
	
	
	/**
	 * Method to count the number of exit nodes in a given function
	 * in both the disassembled binary and the source code
	 * 
	 * @param name
	 * 		Name of the function to count conditionals in
	 * @return
	 * 		Returns a HashMap of String,Long with the binary and source
	 * 		exit node counts
	 * 
	 */
	
	public static HashMap<String, Long> compare_exits(String name) {
		
		String src_name = name.replace("sym_", "");
		long bin_loops = count_exits(name);
		long src_loops = count_exits(src_name);
		
		HashMap<String, Long> counts = new HashMap<String, Long>();
		counts.put("bin", bin_loops);
		counts.put("src", src_loops);
		
		return counts;
	}
	
	
	/**
	 * Method to export the comparisons of the number of loops, conditionals, and 
	 * exit nodes in the disassembled binary and source code for a given function. 
	 * Writes the output to the <function_name>_comparisons.csv
	 * 
	 * @param name
	 * 		Name of the function to compare counts in 
	 * @throws IOException 
	 * 		Throws IO Exception if unable to open and write to the output file		
	 * 
	 */
	
	public static void export_src_comparisons(String name) throws IOException {
		
		String exportPath = "/Users/RyanGoluch/Desktop/"+name+"_comparisons.csv";
		File f = new File(exportPath);
		BufferedWriter b = new BufferedWriter(new FileWriter(f));
		
		b.write("Function Name, # of Loops (Bin), # of Loops (Src), # of Conditionals (Bin), # of Conditionals (Src), # of Exits (Bin), # of Exits (Src)\n");
		b.write(name+",");
		
		HashMap<String, Long> c = new HashMap<String, Long>();
		c = compare_loops(name);
		b.write(c.get("bin") + "," + c.get("src") + ",");
		
		c = compare_conditionals(name);
		b.write(c.get("bin") + "," + c.get("src") + ",");
		
		c = compare_exits(name);
		b.write(c.get("bin") + "," + c.get("src") + ",");
		
		b.flush();
		b.close();
		
	}
	
	
	/**
	 * Method to export all of the comparisons for the number of loops, conditionals, 
	 * and exit nodes for all functions found in the disassembled binary and those functions
	 * that are found in the source code. 
	 * Writes the output to all_comparisons.csv
	 * 
	 * @throws IOException 
	 * 		Throws IO Exception if unable to open and write to the output file
	 * 
	 */
	
	public static void export_all_comparisons() throws IOException {
		
		String exportPath = "/Users/RyanGoluch/Desktop/all_comparisons.csv";
		File f = new File(exportPath);
		BufferedWriter b = new BufferedWriter(new FileWriter(f));
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		b.write("Function Name, # of Loops (Bin), # of Loops (Src), # of Conditionals (Bin), # of Conditionals (Src), # of Exits (Bin), # of Exits (Src)\n");
		b.flush();
		
		for(Node function : functions.eval().nodes()) {
			String name = function.getAttr(XCSG.name).toString();
			HashMap<String, Long> c = new HashMap<String, Long>();
			b.write(name + ",");
			
			c = compare_loops(name);
			b.write(c.get("bin") + "," + c.get("src") + ",");
			
			c = compare_conditionals(name);
			b.write(c.get("bin") + "," + c.get("src") + ",");
			
			c = compare_exits(name);
			b.write(c.get("bin") + "," + c.get("src") + "\n");
			b.flush();
		}
		b.close();
	}
	
}
