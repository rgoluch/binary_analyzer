package com.kcsl.x86.vectors;

import static com.kcsl.x86.subgraphs.SubGraphGenerator.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

public class VectorComparison{

	public static VectorResult createFunctionVectors(String functionName) {
		
		Q binPCG = findSubGraph(functionName);
		String srcName = functionName.substring(4);
		Q srcPCG = singleSrcReturn(srcName);
		
		
//		ArrayList<VectorNode> binVector = new ArrayList<VectorNode>();
//		ArrayList<VectorNode> srcVector = new ArrayList<VectorNode>();
		
		VectorNode binVector[] = new VectorNode[(int)binPCG.eval().nodes().size()];
		VectorNode srcVector[] = new VectorNode[(int)srcPCG.eval().nodes().size()];
		
		System.out.println("Binary Vector: ");
		int i = 0; 
		for (Node n : binPCG.eval().nodes()) {
			String name = n.getAttr(XCSG.name).toString();
			long incoming = n.in().taggedWithAll("bin_induced_edge").size();
			long outgoing = n.out().taggedWithAll("bin_induced_edge").size();
			VectorNode temp = new VectorNode(name, incoming, outgoing);
			
			binVector[i] = temp;
			i++;
			System.out.println("["+incoming+","+outgoing+"]");
		}
		
		System.out.println("Source Vector: ");
		
		i = 0;
		for (Node n : srcPCG.eval().nodes()) {
			String name = n.getAttr(XCSG.name).toString();
			long incoming = n.in().taggedWithAll("src_induced_edge").size();
			long outgoing = n.out().taggedWithAll("src_induced_edge").size();
			VectorNode temp = new VectorNode(name, incoming, outgoing);
			
			srcVector[i] = temp; 
			i++;
			System.out.println("["+incoming+","+outgoing+"]");

		}
		
		VectorResult r = new VectorResult(binVector, srcVector);
		return r;
	}
	
	
	public static void exportSortedVectorStats() throws IOException {
		
		String vectorsPath = "/Users/RyanGoluch/Desktop/Masters_Work/isomorphism_checking/vectors.csv";
		File vectorsFile = new File(vectorsPath);
		BufferedWriter vectorsWriter = new BufferedWriter(new FileWriter(vectorsFile));
		vectorsWriter.write("Function Name, Vector, Vector Size, Complete Match\n");
		
		int bin_gt_src = 0; 
		int bin_lt_src = 0; 
		int bin_eq_src = 0; 
		int bin_id_src = 0;
		
		Comparator<VectorNode> comp = new Comparator<VectorNode>() {
			@Override
			public int compare(VectorNode o1, VectorNode o2) {
				
				//incoming 1 < incoming 2
				if(o1.getIncoming() < o2.getIncoming()) {
					return -1; 
				}
				//incoming 1 == incoming 2, check the outgoing 
				else if(o1.getIncoming() == o2.getIncoming()) {
					if(o1.getOutgoing() < o2.getOutgoing()) {
						return 1; 
					}
				}
				//return 0 if incoming 1 == incoming 2 and outgoing 1 == outgoing 2
				return 0;
			}
		};
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		for(Node function : functions.eval().nodes()) {

			String functionName = function.getAttr(XCSG.name).toString();
			System.out.println(functionName);

			if(functionName.contains("setupStack") || functionName.contains("test")) {
				continue;
			}
			
			VectorResult toSort = createFunctionVectors(functionName);
			VectorNode[] bin = toSort.getBinaryArray();
			VectorNode[] src = toSort.getSrcArray();
			
			if(bin.length > src.length) {
				bin_gt_src++;
			}
			
			if(bin.length < src.length) {
				bin_lt_src++;
			}
			
			if(bin.length == src.length) {
				bin_eq_src++;
			}
		
			Arrays.sort(bin, comp);
			Arrays.sort(src, comp);
			
			if(bin.equals(src)) {
				bin_id_src++;
			}
			
			vectorsWriter.write(functionName+",");
			
			vectorsWriter.write("[");
			for(int j = 0; j < bin.length; j++) {
				vectorsWriter.write(bin[j].nodeToString());
			}
			vectorsWriter.write("],");
			vectorsWriter.write(bin.length +"\n");
			
			vectorsWriter.write(functionName.substring(4)+",");
			
			vectorsWriter.write("[");
			for(int j = 0; j < src.length; j++) {
				vectorsWriter.write(src[j].nodeToString());
			}
			vectorsWriter.write("],");
			vectorsWriter.write(src.length +"\n");
			
			vectorsWriter.flush();
		}
		
		vectorsWriter.write("\n");
		vectorsWriter.write("Vector Counts:\n");
		vectorsWriter.write("Bin Total > Src Total, Bin Total < Src Total, Bin Total == Src Total, Bin Matching Src\n");
		vectorsWriter.write(bin_gt_src + "," + bin_lt_src + "," + bin_eq_src + "," + bin_id_src);		
		vectorsWriter.flush();
		
		vectorsWriter.close();
	}
	
}
