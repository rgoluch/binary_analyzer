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

	public static void main(String[] args) throws FileNotFoundException {
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
		File dot = new File("/Users/RyanGoluch/Desktop/xsh_sleep.dot");
		Scanner s = new Scanner(dot);

		while(s.hasNextLine()) {
			String data = s.nextLine();
			if(data.contains("[URL")) {
				Node n = Graph.U.createNode(); 
				String addr = data.subSequence(2, 12).toString();
				nodeMap.put(addr, n);
			}
			if(data.contains("->")) {
				//Extract the addresses of the from and to nodes in DOT file
				String from = data.subSequence(2, 12).toString();
				String to = data.subSequence(18, 28).toString();
				
				//Create the Atlas nodes and add necessary tags
				Node fromNode = nodeMap.get(from);
				fromNode.putAttr(XCSG.name, "from");
				fromNode.tag(XCSG.ControlFlow_Node);
				
				Node toNode = nodeMap.get(to);
				toNode.putAttr(XCSG.name, "to");
				toNode.tag(XCSG.ControlFlow_Node);
				
				Edge e = Graph.U.createEdge(fromNode, toNode);
				e.tag(XCSG.ControlFlow_Edge);
			}
			
		}
		s.close();
	}

}
