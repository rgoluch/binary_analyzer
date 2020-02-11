package com.kcsl.x86;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.HashMap;
import java.util.Map;
import java.util.Scanner;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.core.xcsg.XCSG.*;

public class Importer {

	public static void main() throws FileNotFoundException {
		// HashMap of Node for further access
		Map<String,Node> nodeMap = new HashMap<String,Node>();
		Node fromN = Graph.U.createNode();
		Node toN = Graph.U.createNode();
		Edge e_temp = Graph.U.createEdge(fromN, toN);
		
		fromN.putAttr(XCSG.name, "from");
		toN.putAttr(XCSG.name, "to");
		// edge labels optional
		 e_temp.putAttr(XCSG.name, "myEdge");
		
		fromN.tag(XCSG.ControlFlow_Node);
		toN.tag(XCSG.ControlFlow_Node);
		e_temp.tag(XCSG.ControlFlow_Edge);
		
		//read in and parse .dot file
		File dot = new File("/Users/RyanGoluch/Desktop/Research/kothari_490/xsh_date.dot");
		Scanner s = new Scanner(dot);

		while(s.hasNextLine()) {
			String data = s.nextLine();
			if(data.contains("[URL")) {
				Node n = Graph.U.createNode(); 
				String addr = data.subSequence(2, 12).toString();
				String label = data.split("label=")[1];
				label = label.replace("\"", "");
				label = label.replace("]", "");
				label = label.replace("\\l", "\n");
				n.putAttr(XCSG.name, label);
				nodeMap.put(addr, n);
			}
			if(data.contains("->")) {
				data = data.replaceAll("\\s+", "");
				//Extract the addresses of the from and to nodes in DOT file
				String from = data.split("->")[0];
				from = from.replaceAll("\"", "");
				String temp = data.split("->")[1];
				String to = temp.split("\\[")[0];
				to = to.replaceAll("\"", "");
				
				//Create the Atlas nodes and add necessary tags
				Node fromNode = nodeMap.get(from);
				fromNode.tag(XCSG.ControlFlow_Node);
				fromNode.tag("my_node");
				
				Node toNode = nodeMap.get(to);
				toNode.tag(XCSG.ControlFlow_Node);
				toNode.tag("my_node");
				
				Edge e = Graph.U.createEdge(fromNode, toNode);
				e.tag(XCSG.ControlFlow_Edge);
				e.tag("my_edge");
			}
			
		}
		s.close();
	}

}
