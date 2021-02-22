package com.kcsl.x86.importers;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FilenameFilter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Scanner;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

import static com.kcsl.x86.support.SupportMethods.*;
import static com.kcsl.x86.Importer.*;

/**
 * 
 * @author RyanGoluch
 *
 */

public class RadareImporter {
	
	private static ArrayList<Node> function_nodes = new ArrayList<Node>();
	
	/**
	 * 
	 * @throws FileNotFoundException
	 */
	
	public static void import_radare() throws FileNotFoundException {
			
			// HashMap of Node for further access
			Map<String,Node> nodeMap = new HashMap<String,Node>();
			
			ArrayList<String> functionNames = new ArrayList<String>();
			
			//read in and parse .dot files from dot_graphs dir
			String path = "/Users/RyanGoluch/Desktop/Research/kothari_490/com.kcsl.x86/dot_graphs";
			String path2 = "/Users/RyanGoluch/Desktop/Research/kothari_490/com.kcsl.x86/class_dot_graphs/dot_graphs/";
//			String path3 = "/Users/RyanGoluch/Desktop/Research/kothari_490/com.kcsl.x86/ppc_dot_graphs/dot_graphs/";
			
			String paths[] = {path2} ;
//					path2, path3};
			
			for (String p : paths) {
				
				File dir = new File(p);
				File[] dirList = dir.listFiles(new FilenameFilter() {
					@Override
					public boolean accept(File dir, String name) {
						return name.endsWith(".dot");
					}
				});
				
				int count = 0;
				boolean cmp = true;
				boolean strnlenCmp = true;
				for(File dot : dirList) {
					ArrayList<Node> indexedNodes = new ArrayList<Node>();
					
					//check to make sure that this condition is needed
					if (dot.exists()) {
						Node functionName = Graph.U.createNode();
						functionName.putAttr(XCSG.name, "sym_"+dot.getName().replace(".dot", ""));
						functionName.tag(XCSG.Function);
						functionName.tag("binary_function");
						functionName.tag("radare_function");
						
						if (p.equals(path)) {
							functionName.tag("new_xinu");
						}
						else if (p.equals(path2)) {
							functionName.tag("class_xinu");
							functionName.removeAttr(XCSG.name);
							functionName.putAttr(XCSG.name, "class_"+dot.getName().replace(".dot", ""));
						}
//						else if (p.equals(path3)) {
//							functionName.tag("ppc_xinu");
//							functionName.removeAttr(XCSG.name);
//							functionName.putAttr(XCSG.name, "ppc_"+dot.getName().replace(".dot", ""));
//						}
						
						
						//Creation of consolidated exit node
						//Comment out lines 68-75 for original exit points
						Node exit = Graph.U.createNode();
						exit.putAttr(XCSG.name, "binary exit");
						exit.tag("my_node");
						exit.tag("bin_node");
						exit.tag("single_exit");
						exit.tag("bin_exit");
						exit.tag(XCSG.controlFlowExitPoint);
						exit.tag(XCSG.ControlFlow_Node);
						Edge functionExit = Graph.U.createEdge(functionName, exit);
						functionExit.tag(XCSG.Contains);
						
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
								
								if (label.contains("slti")) {
									if (!functionNames.contains(functionName.getAttr(XCSG.name))) {
										functionNames.add(functionName.getAttr(XCSG.name).toString());
									}
//									System.out.println(functionName.getAttr(XCSG.name));
								}
								
								
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
								
								//Get the edge color to properly mark true and false edges later on
								String color = temp.split("\\[color=")[1];
								color = color.replaceAll("];", "");
								color = color.replaceAll("\"", "");
								
								//Create the Atlas nodes and add necessary tags
								Node fromNode = nodeMap.get(from);
								
								if (functionName.getAttr(XCSG.name).equals("sym_strcmp") && cmp) {
									fromNode.tag(XCSG.controlFlowRoot);
									fromNode.tag(XCSG.ControlFlowLoopCondition);
									cmp = false;
								}
								
								if (functionName.getAttr(XCSG.name).equals("sym_strnlen") && strnlenCmp) {
									fromNode.tag(XCSG.controlFlowRoot);
									strnlenCmp = false;
								}
								
								indexedNodes.add(fromNode);
								
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
									
									//Mark true and false edges based on dot file edge color
									if (color.contentEquals("#13a10e")) {
										e.putAttr(XCSG.conditionValue, true);
										e.putAttr(XCSG.name, "true");
									}
									else if (color.contentEquals("#c50f1f")) {
										e.putAttr(XCSG.conditionValue, false);
										e.putAttr(XCSG.name, "false");
									}
							
									if(from.contains(to)) {
										fromNode.tag("self_loop_node");
										Graph.U.delete(e);									
									}
								}
							}
							
						}
						s.close();
					}
					
				}
				
				//Go through all of the nodes that are created and tag all loops and conditionals
				Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
				
				for(Node function : functions.eval().nodes()) {
					String name = function.getAttr(XCSG.name).toString();
					//Toggle which line is commented out depending on if single return or original returns
					//being used
//					tag_binary_exits(name);
					tag_binary_single_exits(name);
					tag_binary_branches(name);
					tag_binary_loops(name);
					tag_binary_ifs(name);
					
				}
			}
			
			
//			for (String s : functionNames) {
//				System.out.println(s);
//			}
			
//			System.out.println(count);
			//create a new node
			//XCSG.name, name of function (differentiate from source)
			//tag as XCSG.Function
			//Node fn = Graph.U.createNode();
			//create edge between fn and all other control flow nodes
			//tag it as XCSG.Contains
		}
		
}
