package com.se421.paths.results;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.log.Log;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.script.CommonQueries;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.se421.paths.algorithms.PathCounter.CountingResult;
import com.se421.paths.algorithms.counting.DFSPathCounter;
import com.se421.paths.algorithms.counting.MultiplicitiesPathCounter;
import com.se421.paths.support.SetDefinitions;

/*
 * Use this code to export results of your implementation
 * 
 * @author Payas Awadhutkar
 */

public class ExportResults {

	protected static final String resultsPath = System.getProperty("user.home") + "/Desktop/Results.csv";
	
	protected static final String headers = "Function Name,numPaths (NonLinear),additions (NonLinear),numPaths (Linear),additions (Linear)\n";
	
	public static void export() {
		try {
			File results = new File(resultsPath);
			BufferedWriter resultsWriter = new BufferedWriter(new FileWriter(results));
			resultsWriter.write(headers);
			DFSPathCounter nonLinearCounter = new DFSPathCounter();
			MultiplicitiesPathCounter linearCounter = new MultiplicitiesPathCounter();
			
			// We will now generate the results for all the functions in the graph database.
			// It is assumed that you have XINU mapped into Atlas before you run this code.
			Q app = SetDefinitions.app();
		 	Q functions = app.nodes(XCSG.Function);
			for(Node function : functions.eval().nodes()) {
				Q cfg = CommonQueries.cfg(Common.toQ(function));
				CountingResult nonLinear = nonLinearCounter.countPaths(cfg);
				CountingResult linear = linearCounter.countPaths(cfg);
				
				// function name
				resultsWriter.write(function.getAttr(XCSG.name) + ",");
				
				// number of paths according to nonLinear algorithm
				resultsWriter.write(nonLinear.getPaths() + ",");
				
				// number of additions by nonLinear algorithm
				resultsWriter.write(nonLinear.getAdditions() + ",");
				
				// number of paths according to linear algorithm
				resultsWriter.write(linear.getPaths() + ",");
				
				// number of additions by linear algorithm
				resultsWriter.write(linear.getAdditions() + "\n");
				
				// flushing the buffer
				resultsWriter.flush();
			}
			
			resultsWriter.close();
			
		} catch(FileNotFoundException e) {
			Log.error(e.getMessage(), e);
		} catch(IOException e) {
			Log.error(e.getMessage(), e);
		} finally {
			
		}
	}
	
}
