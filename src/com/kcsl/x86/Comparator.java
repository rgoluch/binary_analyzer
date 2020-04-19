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
	 * 
	 * @param name
	 * @return 
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
	 * 
	 * @param name
	 * @return
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
	 * 
	 * @param name
	 * @return
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
	 * 
	 * @param name
	 * @throws IOException 
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
	 * @throws IOException 
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
