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
//import org.radare.r2pipe.R2Pipe;
//import com.kcsl.paths;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.script.CommonQueries;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.ui.viewer.graph.DisplayUtil;
import com.ensoftcorp.atlas.ui.viewer.graph.SaveUtil;
import com.ensoftcorp.open.commons.algorithms.LoopIdentification;
import com.se421.paths.algorithms.PathCounter.CountingResult;
import com.se421.paths.algorithms.counting.MultiplicitiesPathCounter;

public class Importer {

	protected static final String resultsPath = "/Users/RyanGoluch/Desktop/My_Results.csv";
	
	protected static final String graphPath = "/Users/RyanGoluch/Desktop/";
	
	protected static final String functionPath = "/Users/RyanGoluch/Desktop/source_function_list.csv";
	
	protected static final String binaryPath = "/Users/RyanGoluch/Desktop/binary_function_list.csv";
	
	protected static final String headers = "Function Name,numPaths (Linear),additions (Linear)\n";
	
	private static ArrayList<Node> function_nodes = new ArrayList<Node>();

	
	/**
	 * TODO
	 * @throws IOException
	 */
	
	public static void check_difference() throws IOException {
		Q functions = Common.universe().nodesTaggedWithAll(XCSG.Language.C, XCSG.Function);
		String filePath = "/Users/RyanGoluch/Desktop/source_functions.csv";
		File source = new File(filePath);
		BufferedWriter resultsWriter = new BufferedWriter(new FileWriter(source));
		
		for(Node f : functions.eval().nodes()) {
			String name = f.getAttr(XCSG.name).toString();
			String binary = "sym_"+name;
			
			//get the functions that are in source and not in binary
			Q binary_function = Query.universe().selectNode(XCSG.name, binary);
			if(binary_function.eval().nodes().size() == 0) {
				System.out.println(name);
				resultsWriter.write(name+"\n");
				resultsWriter.flush();
			}
		}
		resultsWriter.close();
	}
	
	
	/**
	 * TODO
	 * @throws IOException
	 */
	
	public static void source_functions() throws IOException {
		Q functions = Common.universe().nodesTaggedWithAll(XCSG.Language.C, XCSG.Function);
		File source = new File(functionPath);
		BufferedWriter resultsWriter = new BufferedWriter(new FileWriter(source));
		
//		resultsWriter.write("# of Functions: " + functions.eval().nodes().size() + "\n");
//		resultsWriter.flush();
		
		for (Node f : functions.eval().nodes()) {
			String name = f.getAttr(XCSG.name).toString();
			resultsWriter.write(name+"\n");
			resultsWriter.flush();
		}
		resultsWriter.close();
	}
	
	
	/**
	 * TODO
	 * @throws IOException
	 */
	
	public static void binary_functions() throws IOException {
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		File binary = new File(binaryPath);
		BufferedWriter binaryWriter = new BufferedWriter(new FileWriter(binary));
		
//		binaryWriter.write("# of Functions: " + functions.eval().nodes().size() + "\n");
//		binaryWriter.flush();
		
		for (Node f : functions.eval().nodes()) {
			String name = f.getAttr(XCSG.name).toString();
			name = name.split("sym_")[1];
			binaryWriter.write(name+"\n");
			binaryWriter.flush();
		}
		binaryWriter.close();
	}
	
	
	/**
	 * TODO
	 * @throws FileNotFoundException
	 */
	
	public static void main() throws FileNotFoundException {
		// HashMap of Node for further access
		Map<String,Node> nodeMap = new HashMap<String,Node>();
		
		//read in and parse .dot files from dot_graphs dir
		String path = "/Users/RyanGoluch/Desktop/Research/kothari_490/com.kcsl.x86/dot_graphs";
		File dir = new File(path);
		File[] dirList = dir.listFiles(new FilenameFilter() {
			@Override
			public boolean accept(File dir, String name) {
				return name.endsWith(".dot");
			}
		});
		int count = 0; 
		for(File dot : dirList) {
			
			//check to make sure that this condition is needed
			if (dot.exists()) {
//				count++;
//				System.out.println("Count: " +count+" Function: "+dot.getName());
				Node functionName = Graph.U.createNode();
				functionName.putAttr(XCSG.name, "sym_"+dot.getName().replace(".dot", ""));
				functionName.tag(XCSG.Function);
				functionName.tag("binary_function");
				
				function_nodes.add(functionName);
				Scanner s = new Scanner(dot);
				
				while(s.hasNextLine()) {
					String data = s.nextLine();
					if(data.contains("[URL")) {
						//Create control flow nodes with labels
						Node n = Graph.U.createNode(); 
						n.tag(XCSG.ControlFlow_Node);
						n.tag("my_node");
						
						String addr = data.subSequence(2, 12).toString();
						String label = data.split("label=")[1];
						label = label.replace("\"", "");
						label = label.replace("]", "");
						label = label.replace("\\l", "\n");
						n.putAttr(XCSG.name, label);
						
						//Map all control flow nodes to function container
						Edge temp = Graph.U.createEdge(functionName, n);
						temp.tag(XCSG.Contains);
						nodeMap.put(addr, n);
					}
					else if(data.contains("->")) {
						data = data.replaceAll("\\s+", "");
						//Extract the addresses of the from and to nodes in DOT file
						String from = data.split("->")[0];
						from = from.replaceAll("\"", "");
						String temp = data.split("->")[1];
						String to = temp.split("\\[color")[0];
						to = to.replaceAll("\"", "");
						
						//Create the Atlas nodes and add necessary tags
						Node fromNode = nodeMap.get(from);
						
						//Handling exit nodes for test files in test directory
						if(nodeMap.get(to) == null) {
							Node exitNode = Graph.U.createNode();
							exitNode.putAttr(XCSG.name, to);
							Edge x = Graph.U.createEdge(fromNode, exitNode);
							x.tag(XCSG.ControlFlow_Edge);
							x.tag("my_edge");
							
						}else {
							Node toNode = nodeMap.get(to);
							toNode.tag(XCSG.ControlFlow_Node);
							toNode.tag("my_node");
							
							Edge e = Graph.U.createEdge(fromNode, toNode);
							e.tag(XCSG.ControlFlow_Edge);
							e.tag("my_edge");
							
							if(from.contains(to)) {
								fromNode.tag("self_loop");
//								fromNode.tag(XCSG.Loop);
//								Query.universe().roots()
								
							}
						}
					}
					
				}
				s.close();
			}
			
		}
		
		
		//create a new node
		//XCSG.name, name of function (differentiate from source)
		//tag as XCSG.Function
		//Node fn = Graph.U.createNode();
		//create edge between fn and all other control flow nodes
		//tag it as XCSG.Contains
	}
	
	
	/**
	 * TODO
	 * @param name
	 * @return
	 */
	
	public static Q my_function(String name) {
		Q f = Query.universe().nodes(XCSG.Function);
		Q found = f.selectNode(XCSG.name, name);
		return found;
	}
	
	
	/**
	 * Creates the control flow graph of the given function from
	 * the disassembled binary
	 * @param f
	 * 		Variable that holds what is returned from my_function. 
	 * 		Should be a function within the disassembled binary. 
	 * @return
	 * 		A CFG for the given binary function 
	 */
	
	public static Q my_cfg(Q f) {
		return f.contained().nodes(XCSG.ControlFlow_Node).induce(Query.universe().edges(XCSG.ControlFlow_Edge));
	}
	
	
	/**
	 * 
	 * @throws IOException
	 */
	
	public static void export_counts() throws IOException {

			File results = new File(resultsPath);
//			File source = new File(functionPath);
			BufferedWriter resultsWriter = new BufferedWriter(new FileWriter(results));
//			BufferedWriter functionWriter = new BufferedWriter(new FileWriter(source));
			resultsWriter.write(headers);
			MultiplicitiesPathCounter linearCounter = new MultiplicitiesPathCounter();
			
			
			ArrayList<String> skips = new ArrayList<String>();
//			skips.add("test_libString");
//			skips.add("sym_copyhandler");
//			skips.add("sym_strcmp");
//			skips.add("sym_loc");
//			skips.add("sym_memzero");
//			skips.add()
			
			int count = 0;
			// We will now generate the results for all the functions in the graph database.
			// It is assumed that you have XINU mapped into Atlas before you run this code.
//			Q app = SetDefinitions.app();
		 	Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		 			//app.nodes(XCSG.Function).nodesTaggedWithAll("my_function");
		 	int i = 0;
		 	
			for(Node function : functions.eval().nodes()) {
				String name = function.getAttr(XCSG.name).toString();
				
//				functionWriter.write(name.toString() + "\n");
				
//				if(skips.contains(name)) {
//					continue;
//				}
				
				Q temp = Common.toQ(function);
				Graph c = my_cfg(temp).eval();
//				DisplayUtil.displayGraph(c);
				System.out.println(function.getAttr(XCSG.name) + " nodes: "+c.nodes().size());
			
				long check = c.nodes().tagged("my_node").size();
				
				if (c.nodes().tagged("my_node").size() == 1) {
					// function name
					resultsWriter.write(function.getAttr(XCSG.name) + ",");
					
					// number of paths according to linear algorithm
					resultsWriter.write("1" + ",");
					
					// number of additions by linear algorithm
					resultsWriter.write("0" + "\n");
					
				}else {
					Q r = Common.toQ(c).roots();
					if(CommonQueries.isEmpty(r)) {
						r = Common.toQ(c).nodes("self_loop");
//						DisplayUtil.displayGraph(c);
					}
					
					if(CommonQueries.isEmpty(r)) {
						SaveUtil.saveGraph(new File(graphPath+"cfg_"+i+".png"), c);
						i++;
					}
					else {
						LoopIdentification l = new LoopIdentification(c, r.eval().nodes().one());
						CountingResult linear = linearCounter.countPaths(Common.toQ(c));
						
						// function name
						resultsWriter.write(function.getAttr(XCSG.name) + ",");
						
						// number of paths according to linear algorithm
						resultsWriter.write(linear.getPaths() + ",");
						
						// number of additions by linear algorithm
						resultsWriter.write(linear.getAdditions() + "\n");
					}
					
				}
				
				
				// flushing the buffer
				resultsWriter.flush();
//				functionWriter.flush();
			}
			
			resultsWriter.close();
//			functionWriter.close();
	}
}
