package com.kcsl.x86.short_circuit;

import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasHashSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

public class ShortCircuitChecking {
	
	protected static final String OR = "||";
	protected static final String AND = "&&";
	protected static final String LAST = "sc_end";

	
	public static scInfo scChecker(Q cfg) {
		
		AtlasSet<Node> conditions = cfg.eval().nodes().tagged(XCSG.ControlFlowCondition);
		ArrayList<String> ordering = new ArrayList<String>();
		scInfo scCount = null;
		
		for (Node n : conditions) {
			AtlasSet<Node> toCheck = Common.toQ(n).contained().nodes(XCSG.LogicalOr, XCSG.LogicalAnd).eval().nodes();
			
			if (toCheck.size() > 0) {
				long and = Common.toQ(n).contained().nodes(XCSG.LogicalAnd).eval().nodes().size();
				long or = Common.toQ(n).contained().nodes(XCSG.LogicalOr).eval().nodes().size();
				scCount = new scInfo(toCheck.size(), and, or);
			}
			
			for (Node x : toCheck) {
				ordering.add(x.getAttr(XCSG.name).toString());
			}
		}
		
		System.out.println(ordering.toString());
//		System.out.println("Total # Nodes with SC Conditions: " + scCount);
		
		return scCount;
	}
	
	
	public static Q scTransform(String name) {
		
		Q f = my_function(name);	
		Q c = my_cfg(f);
		
		Node functionNode = Graph.U.createNode();
		functionNode.putAttr(XCSG.name, "sc_transform_"+name);
		functionNode.tag(XCSG.Function);
		functionNode.tag("sc_graph");

		AtlasSet<Node> conditions = c.eval().nodes().tagged(XCSG.ControlFlowCondition);
		ArrayList<String> ordering = new ArrayList<String>();
		ArrayList<Node> scNodes = new ArrayList<Node>();
		
		for (Node n : conditions) {
			AtlasSet<Node> toCheck = Common.toQ(n).contained().nodes(XCSG.LogicalOr, XCSG.LogicalAnd).eval().nodes();
			if (toCheck.size() > 0) {
				scNodes.add(n);
			}
		}
		
		ArrayList<Node> taggedNodes = new ArrayList<Node>();
		Node trueDest = null;
		Node falseDest = null;
		
		for (Node n : c.eval().nodes()) {
			
			if(!scNodes.contains(n)) {
				n.tag("sc_graph");
			}
		}
		
		for (Edge e : c.eval().edges().tagged(XCSG.ControlFlow_Edge)) {
			e.tag("sc_edge");
		}
		
		
		Map<Node,Node> addedToGraph = new HashMap<Node,Node>();
//		System.out.println(c.eval().edges().tagged(XCSG.ControlFlow_Edge).size());
		
		for (Edge e : c.eval().edges().tagged(XCSG.ControlFlow_Edge)) {
			
			if (e.from().taggedWith("sc_graph") && e.to().taggedWith("sc_graph")) {
				Node tempFrom = Graph.U.createNode();
				Node tempTo = Graph.U.createNode();
				
				String fromName = e.from().getAttr(XCSG.name).toString();
				String toName = e.to().getAttr(XCSG.name).toString();
				
				tempFrom.putAttr(XCSG.name, fromName);
				tempFrom.tag(XCSG.ControlFlow_Node);
				tempFrom.tag("sc_graph");
				
				if (e.from().taggedWith(XCSG.ControlFlowCondition)) {
					tempFrom.tag(XCSG.ControlFlowCondition);
				}
				
				tempTo.putAttr(XCSG.name, toName);
				tempTo.tag(XCSG.ControlFlow_Node);
				tempTo.tag("sc_graph");
				
				if (e.to().taggedWith(XCSG.ControlFlowCondition)) {
					tempTo.tag(XCSG.ControlFlowCondition);
				}
				
				Node checkingResultFrom  = addedToGraph.get(e.from());
				Node checkingResultTo = addedToGraph.get(e.to());
				Edge tempEdge = null;
				
				if (checkingResultFrom == null && checkingResultTo == null) {
					Edge eFrom = Graph.U.createEdge(functionNode, tempFrom);
					eFrom.tag(XCSG.Contains);
					
					Edge eTo = Graph.U.createEdge(functionNode, tempTo);
					eTo.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(tempFrom, tempTo);
					tempEdge.tag("sc_edge");
					tempEdge.tag(XCSG.ControlFlow_Edge);
					
					addedToGraph.put(e.from(), tempFrom);
					addedToGraph.put(e.to(), tempTo);
				}
				else if (checkingResultFrom != null && checkingResultTo == null) {
					Edge eTo = Graph.U.createEdge(functionNode, tempTo);
					eTo.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(checkingResultFrom, tempTo);
					tempEdge.tag("sc_edge");
					tempEdge.tag(XCSG.ControlFlow_Edge);
					
					addedToGraph.put(e.to(), tempTo);
				}
				else if (checkingResultFrom == null && checkingResultTo != null) {
					Edge eFrom = Graph.U.createEdge(functionNode, tempFrom);
					eFrom.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(tempFrom, checkingResultTo);
					tempEdge.tag("sc_edge");
					tempEdge.tag(XCSG.ControlFlow_Edge);
					
					addedToGraph.put(e.from(), tempFrom);
				}
				else if (checkingResultFrom != null && checkingResultTo != null) {
					tempEdge = Graph.U.createEdge(checkingResultFrom, checkingResultTo);
					tempEdge.tag("sc_edge");
					tempEdge.tag(XCSG.ControlFlow_Edge);
				}
				
				if (e.to().hasAttr(XCSG.conditionValue)) {
					if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
						tempEdge.putAttr(XCSG.conditionValue, "true");
					}else {
						tempEdge.putAttr(XCSG.conditionValue, "false");
					}
				}
			}
		}
		
		
		for (Node x : scNodes) {
			
			AtlasSet<Edge> outEdges = x.out().tagged(XCSG.ControlFlow_Edge);
			Edge o1 = null;
			Edge o2 = null;
			
			for (Edge e : outEdges) {
				if (o1 == null) {
					o1 = e;
				}else {
					o2 = e;
				}
			}
			
			if (o1.getAttr(XCSG.conditionValue).toString().contains("true")) {
				trueDest = addedToGraph.get(o1.to());
				falseDest = addedToGraph.get(o2.to());
			}else {
				falseDest = addedToGraph.get(o1.to());
				trueDest = addedToGraph.get(o2.to());
			}
			
			AtlasSet<Node> toCheck = Common.toQ(x).contained().nodes(XCSG.LogicalOr, XCSG.LogicalAnd).eval().nodes();

			for (Node q : toCheck) {
				ordering.add(q.getAttr(XCSG.name).toString());
			}

			scNode[] nodes = createScNodes(ordering, x);
			ArrayList<Node> scNodesInGraph = new ArrayList<Node>();
			
			if (nodes.length > 2) {
				
				for(int j = 0; j < nodes.length; j++) {
					Node temp1 = Graph.U.createNode();
					temp1.putAttr(XCSG.name, nodes[j].getCondition());
					temp1.tag(XCSG.ControlFlowCondition);
					temp1.tag("sc_graph");
					
					scNodesInGraph.add(temp1);
				
					Edge e1 = Graph.U.createEdge(functionNode, temp1);
					e1.tag(XCSG.Contains);
				}
				
				for (int m = 0; m < scNodesInGraph.size(); m++) {
					scNode checking = nodes[m];
					Node checkingNode = scNodesInGraph.get(m);
			
					if(checking.getOperator().contains(LAST)) {
						checking.setTrueDest(checkingNode, trueDest);
						checking.setFalseDest(checkingNode, falseDest);
					}
				}
				
				for (int m = scNodesInGraph.size()-1; m >= 0; m--) {
					scNode checking = nodes[m];
					Node checkingNode = scNodesInGraph.get(m);
					
					if(checking.getOperator().contains(AND)) {
						checking.setTrueDest(checkingNode, scNodesInGraph.get(m+1));
						checking.setFalseDest(checkingNode, nodes[m+1].getFalseDest());
					}
					if(checking.getOperator().contains(OR)) {
						checking.setFalseDest(checkingNode, scNodesInGraph.get(m+1));
						checking.setTrueDest(checkingNode, nodes[m+1].getTrueDest());
					}
				}
			}
			
			else {
				for (String s : ordering) {

					String tempName1 = x.getAttr(XCSG.name).toString().split(s)[0];
					String tempName2 = x.getAttr(XCSG.name).toString().split(s)[1];
					
					Node temp1 = Graph.U.createNode();
					temp1.putAttr(XCSG.name, tempName1);
					temp1.tag(XCSG.ControlFlowCondition);
					temp1.tag("sc_graph");
					
					Node temp2 = Graph.U.createNode();
					temp2.putAttr(XCSG.name, tempName2);
					temp2.tag(XCSG.ControlFlowCondition);
					temp2.tag("sc_graph");
					
					Edge e1 = Graph.U.createEdge(functionNode, temp1);
					e1.tag(XCSG.Contains);
					
					Edge e2 = Graph.U.createEdge(functionNode, temp2);
					e2.tag(XCSG.Contains);
					
					
					if (s.contains("&&")) {
						Edge tempTrue = Graph.U.createEdge(temp1, temp2);
						tempTrue.tag(XCSG.ControlFlow_Edge);
						tempTrue.putAttr(XCSG.conditionValue, "true");
						tempTrue.tag("sc_edge");
						
						Edge tempFalse = Graph.U.createEdge(temp1, falseDest);
						tempFalse.tag(XCSG.ControlFlow_Edge);
						tempFalse.putAttr(XCSG.conditionValue, "false");
						tempFalse.tag("sc_edge");
						
						Edge tempTrue2 = Graph.U.createEdge(temp2, trueDest);
						tempTrue2.tag(XCSG.ControlFlow_Edge);
						tempTrue2.putAttr(XCSG.conditionValue, "true");
						tempTrue2.tag("sc_edge");
						
						Edge tempFalse2 = Graph.U.createEdge(temp2, falseDest);
						tempFalse2.tag(XCSG.ControlFlow_Edge);
						tempFalse2.putAttr(XCSG.conditionValue, "false");
						tempFalse2.tag("sc_edge");
					}
					
					else if (s.contains("||")) {
						Edge tempTrue = Graph.U.createEdge(temp1, temp2);
						tempTrue.tag(XCSG.ControlFlow_Edge);
						tempTrue.putAttr(XCSG.conditionValue, "false");
						
						Edge tempFalse = Graph.U.createEdge(temp1, trueDest);
						tempFalse.tag(XCSG.ControlFlow_Edge);
						tempFalse.putAttr(XCSG.conditionValue, "true");
						
						Edge tempTrue2 = Graph.U.createEdge(temp2, trueDest);
						tempTrue2.tag(XCSG.ControlFlow_Edge);
						tempTrue2.putAttr(XCSG.conditionValue, "true");
						
						Edge tempFalse2 = Graph.U.createEdge(temp2, falseDest);
						tempFalse2.tag(XCSG.ControlFlow_Edge);
						tempFalse2.putAttr(XCSG.conditionValue, "false");
					}
				}
			}
			
			
			
		}
		

		Q x = my_function(functionNode.getAttr(XCSG.name).toString());
		Q sc_cfg = my_cfg(x);
		
		return sc_cfg.nodes("sc_graph").induce(Query.universe().edges("sc_edge"));
	}
	
	
	public static scNode[] createScNodes(ArrayList<String> ordering, Node x) {
		
//		ArrayList<String> updatedOrdering = new ArrayList<String>();
//		Set<scNode> finalOrdering = new HashSet<scNode>();
//		ArrayList<String> added = new ArrayList<String>();
		scNode[] conditions = new scNode[ordering.size()+1];
		int j = 0; 
		
		String name = x.getAttr(XCSG.name).toString();
		String[] parts = name.split(" ");
		
		for (int p = 0; p < parts.length-1; p++) {
			String toCheck = parts[p];
			if(toCheck.contains(AND) || toCheck.contains(OR)) {
				continue;
			}else {
				if (parts[p+1].contains(AND)) {
					scNode tempSCNode = new scNode(toCheck, AND);
					conditions[j] = tempSCNode;
					j++;
				}
				if (parts[p+1].contains(OR)) {
					scNode tempSCNode = new scNode(toCheck, OR);
					conditions[j] = tempSCNode;
					j++;
				}
			}
		}
		
		scNode temp = new scNode(parts[parts.length-1], LAST);
		conditions[conditions.length-1] = temp;
		
		
		
		
//		//working to isolate conditions
//		for (String a : ordering) {
////			String temp;
////			String temp2; 
//			String[] toIsolate;
//			//get conditions and remove spaces for easier comparison amongst strings
//			if (a.contains("||")) {
////				temp = x.getAttr(XCSG.name).toString().split("\\|\\|")[0];
////				temp = temp.replaceAll("\\s+", "");
////
////				temp2 = x.getAttr(XCSG.name).toString().split("\\|\\|")[1];
////				temp2 = temp2.replaceAll("\\s+", "");
////				updatedOrdering.add(temp);
////				updatedOrdering.add(temp2);
//				
//				toIsolate = x.getAttr(XCSG.name).toString().split("\\|\\|");
//				for (int y = 0; y < toIsolate.length; y++) {
//					updatedOrdering.add(toIsolate[y]);
//				}
//				
//			}else {
////				temp = x.getAttr(XCSG.name).toString().split(a)[0];
////				temp = temp.replaceAll("\\s+", "");
////
////				temp2 = x.getAttr(XCSG.name).toString().split(a)[1];
////				temp2 = temp2.replaceAll("\\s+", "");
////				updatedOrdering.add(temp);
////				updatedOrdering.add(temp2);
//				
//				toIsolate = x.getAttr(XCSG.name).toString().split(a);
//				for (int y = 0; y < toIsolate.length; y++) {
//					updatedOrdering.add(toIsolate[y]);
//				}
//			}
//		}
//	
//		//breaking up any other conditions
//		for(int i = 0; i < updatedOrdering.size(); i++) {
//			String b = updatedOrdering.get(i);
//			while(b.contains("&&") || b.contains("||")) {
//				if (b.contains("&&")) {
//					String[] d = b.split("&&");
//					b = d[0];
//					
//					scNode tempSCNode = new scNode(b, AND);
//					conditions[j] = tempSCNode;
//					j++;
//					finalOrdering.add(tempSCNode);
//					added.add(b);
//					
//					if (!updatedOrdering.contains(d[1]) && (d[1].contains(AND) || d[1].contains(OR))) {
//						updatedOrdering.add(d[1]);
//					}
//				}
//				
//				if (b.contains("||")) {
//					String[] d = b.split("\\|\\|");
//					b = d[0];
//					
//					scNode tempSCNode = new scNode(b, OR);
//					conditions[j] = tempSCNode;
//					j++;
//					finalOrdering.add(tempSCNode);
//					added.add(b);
//					
//					updatedOrdering.set(i, b);
//					if (!updatedOrdering.contains(d[1]) && (d[1].contains(AND) || d[1].contains(OR))) {
//						updatedOrdering.add(d[1]);
//					}
//				}
//			}
//			
//			if (!b.contains(AND) && !b.contains(OR) && !added.contains(b) && !b.contains("if (")) {
//				scNode temp = new scNode(b, LAST);
//				conditions[conditions.length-1] = temp;
////				j++;
//				finalOrdering.add(temp);
//			}
//		}
		
//		scNode[] conditions = new scNode[finalOrdering.size()];
//		finalOrdering.toArray(conditions);
		
		return conditions;
	}
	
	
	private static class scNode{
		private String condition;
		private String operator; 
		private Node truDest; 
		private Node falsDest; 
		
		public scNode(String c, String o) {
			this.condition = c;
			this.operator = o;
		}
		
		public String getCondition() {
			return this.condition;
		}
		
		public String getOperator() {
			return this.operator;
		}
		
		public void setTrueDest(Node temp1, Node temp2) {
			this.truDest = temp2;
			
			Edge tempTrue = Graph.U.createEdge(temp1, temp2);
			tempTrue.tag(XCSG.ControlFlow_Edge);
			tempTrue.putAttr(XCSG.conditionValue, "true");
			tempTrue.tag("sc_edge");
			tempTrue.tag("sc_edge_testing");
		}
		
		public Node getTrueDest() {
			return this.truDest;
		}
		
		public void setFalseDest(Node temp1, Node temp2) {
			this.falsDest = temp2;
			
			Edge tempTrue = Graph.U.createEdge(temp1, temp2);
			tempTrue.tag(XCSG.ControlFlow_Edge);
			tempTrue.putAttr(XCSG.conditionValue, "true");
			tempTrue.tag("sc_edge");
			tempTrue.tag("sc_edge_testing");
		}
		
		public Node getFalseDest() {
			return this.falsDest;
		}
	}
	
	
	private static class scInfo{
		private long conditions; 
		private long ands;
		private long ors;
		
		public scInfo(long c, long a, long o) {
			this.conditions = c; 
			this.ands = a; 
			this.ors = o;
		}
		
		public long getConditions() {
			return this.conditions;
		}
		
		public long getAnds() {
			return this.ands;
		}
		
		public long getOrs() {
			return this.ors;
		}
	}
	
	public static void scCounts() throws IOException {
		
		String scPath = "/Users/RyanGoluch/Desktop/Masters_Work/isomorphism_checking/sc_checking.csv";
		File scFile = new File(scPath);
		BufferedWriter scWriter = new BufferedWriter(new FileWriter(scFile));
		scWriter.write("Function Name, Conditions, Ands, Ors\n");
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		int result = 0; 
		
		for (Node f : functions.eval().nodes()) {
			String functionName = f.getAttr(XCSG.name).toString();
			String srcName = functionName.substring(4);
			
			if (functionName.contains("test")) {
				continue;
			}
			
			Q function = my_function(srcName);
			Q c = my_cfg(function);
			
			scInfo x = scChecker(c);
			
			if (x != null) {
				result++;
				scWriter.write(srcName + "," + x.getConditions() + "," + x.getAnds() + "," +x.getOrs() + "\n");
				scWriter.flush();
			}
		}
		scWriter.close();
		System.out.println("Number of Source Functions w/ SC: " + result);
		
	}

}
