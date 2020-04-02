package com.kcsl.x86;

import static com.kcsl.x86.Importer.*;
import static com.kcsl.x86.Verifier.*;

import java.util.HashMap;

import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

/**
 * 
 * @author RyanGoluch
 *
 */

public class Comparator {
	
	public Comparator(long bin, long src) {
		long binaryCount = bin;
		long srcCount = src;
	}
	
	public Comparator() {
		long binaryCount = 0;
		long srcCount = 0;
	}
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
	 */
	
	public static void export_src_comparisons(String name) {
		
		HashMap<String, Long> c = new HashMap<String, Long>();
		c = compare_loops(name);
		
		
	}
	
	
	/**
	 * 
	 */
	
	public static void export_all_comparisons() {
		
	}
	
}
