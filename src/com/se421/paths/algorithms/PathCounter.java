package com.se421.paths.algorithms;

import com.ensoftcorp.atlas.core.query.Q;

/**
 * A common interface of program path counting algorithms
 *
 * @author Payas Awadhutkar, Ben Holland
 */
public abstract class PathCounter {

	/**
	 * Counts the number of paths in a given control flow graph
	 * @param cfg
	 * @return
	 */
	public abstract CountingResult countPaths(Q cfg);

	/**
	 * Holds a path counting result, which consists of the number of paths counted
	 * and the number of additions performed to compute the result.
	 */
	public static class CountingResult {
		private long additions = 0L;
		private long paths = 0L;

		public CountingResult(long additions, long paths) {
			this.additions = additions;
			this.paths = paths;
		}

		public long getAdditions() {
			return additions;
		}

		public long getPaths() {
			return paths;
		}

		@Override
		public String toString() {
			return "Result [additions=" + additions + ", paths=" + paths + "]";
		}
	}

}
