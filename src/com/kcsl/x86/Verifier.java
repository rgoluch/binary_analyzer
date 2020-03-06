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
import com.kcsl.x86.Importer.*;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.open.commons.algorithms.LoopIdentification;
import com.se421.paths.algorithms.PathCounter.CountingResult;
import com.se421.paths.algorithms.counting.MultiplicitiesPathCounter;

public class Verifier {
	
	/**
	 * TODO
	 */
	
	public static void count_exits(String name) {
		Q function = Importer.my_function(name);
		Q cfg = Importer.my_cfg(function);
		
		
	}
	
	
	/**
	 * TODO
	 */
	
	public static void count_loops(String name) {
		Q function = Importer.my_function(name);
		Q cfg = Importer.my_cfg(function);
	}
	
	
	/**
	 * TODO
	 */
	
	public static void count_conditionals(String name) {
		Q function = Importer.my_function(name);
		Q cfg = Importer.my_cfg(function);
	}
	
	
	/**
	 * TODO
	 */
	
	public static void verify_all(String name){
		Q function = Importer.my_function(name);
		Q cfg = Importer.my_cfg(function);
	}
}
