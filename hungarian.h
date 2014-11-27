// Last edited: 2014-11-27 by skishore
// This file is not copyrighted. It is in the public domain.
//
// Implementation of the Hungarian algorithm for finding minimum perfect
// matchings. Usage:
//  - Compute Cost** cost_matrix, an nxn array where each entry is non-negative
//    and where cost_matrix[x][y] is the cost of matching x with y.
//  - Construct Hungarian(n, cost_matrix). The algorithm runs on construction.
//  - Use GetTotalCost, GetXMatch, and GetYMatch to read the output.
//
// We restrict to integer costs because the algorithm is not numerically stable.
// When all inputs are integers, the intermediate edge weights we compute are
// also guaranteed to be integers.

#ifndef __HUNGARIAN__
#define __HUNGARIAN__

#include <cassert>

typedef int Cost;

namespace {
inline Cost max(Cost a, Cost b) {
  return (a > b ? a : b);
}
}  // namespace

class Hungarian {
 public:
  // cost_matrix must point to an nxn matrix of NON-NEGATIVE Cost values.
  Hungarian(int n_, const Cost** cost_matrix_)
      : n(n_), cost_matrix(new Cost[n*n]), x_match(new int[n]),
        y_match(new int[n]), x_label(new Cost[n]), y_label(new Cost[n]) {
    for (int x = 0; x < n; x++) {
      for (int y = 0; y < n; y++) {
        cost_matrix[n*x+y] = cost_matrix_[x][y];
      }
      // Initially, all vertices are unmatched.
      x_match[x] = -1;
      y_match[x] = -1;
    }
    matched = 0;
    // We first run heuristics that modify the cost matrix - hence the copy.
    // These heuristics do not change the optimal solution, but they allow the
    // algorithm to convert in less than n^2 iterations on easier inputs.
    ReduceCostMatrix();
    FindGreedySolution();
    while (matched < n) {
      const int last_matched = matched;
      RunAugmentationStep();
      assert(matched > last_matched);
      for (int x = 0; x < n; x++) {
        assert(x_match[x] == -1 || GetCost(x, x_match[x]) == 0);
      }
    }
  }

  ~Hungarian() {
    delete cost_matrix;
    delete x_match;
    delete y_match;
    delete x_label;
    delete y_label;
  }

  // Given the original matrix again, return the total cost of the matching.
  Cost GetTotalCost(const Cost** cost_matrix) const {
    Cost score = 0;
    for (int x = 0; x < n; x++) {
      score += cost_matrix[x][x_match[x]];
    }
    return score;
  }

  // Return the y-coordinate that was matched with the given x-coordinate.
  // Note that x-coordinates correspond to the first coordinate of the matrix,
  // so the total cost is given by
  //   sum(x = 0,1,...n) cost_matrix[x][GetXMatch(x)]
  int GetXMatch(int x) {
    return x_match[x];
  }

  // Return the x-coordinate that was matched with the given y-coordinate.
  int GetYMatch(int y) {
    return y_match[y];
  }

 private:
  // The input matrix and its size. We store the matrix in a 1D array and use
  // cost_matrix[n*x+y] to access the (x, y) entry of the matrix.
  int n;
  Cost* cost_matrix;

  // x_match[x] is the y that is currently matched with the given x.
  // If x is unmatched, then x_match[x] will equal -1. y_match is similar.
  int* x_match;
  int* y_match;

  // x_label[x] and y_label[y] are dual variables that satisfy the condition:
  //   cost_matrix[n*x+y] >= x_label[x] + y_label[y]
  // We define the cost of the edge (x, y) to be:
  //   cost(x, y) = cost_matrix[n*x+y] - x_label[x] - y_label[y]
  // An edge is tight if its cost is zero. Throughout this algorithm, we will
  // maintain the invariant that all matched edges have cost zero.
  Cost* x_label;
  Cost* y_label;

  // The number of edges currently matched.
  int matched;

  Cost GetCost(int x, int y) const {
    return cost_matrix[n*x+y] - x_label[x] - y_label[y];
  }

  void Match(int x, int y) {
    x_match[x] = y;
    y_match[y] = x;
  }

  void ReduceCostMatrix() {
    for (int x = 0; x < n; x++) {
      Cost max_cost = 0;
      for (int y = 0; y < n; y++) {
        max_cost = max(max_cost, cost_matrix[n*x+y]);
      }
      for (int y = 0; y < n; y++) {
        cost_matrix[n*x+y] -= max_cost;
      }
      x_label[x] = 0;
    }
    for (int y = 0; y < n; y++) {
      Cost max_cost = 0;
      for (int x = 0; x < n; x++) {
        max_cost = max(max_cost, cost_matrix[n*x+y]);
      }
      for (int x = 0; x < n; x++) {
        cost_matrix[n*x+y] -= max_cost;
      }
      y_label[y] = 0;
    }
  }

  void FindGreedySolution() {
    for (int x = 0; x < n; x++) {
      for (int y = 0; y < n; y++) {
        if (x_match[x] == -1 && y_match[y] == -1 && GetCost(x, y) == 0) {
          Match(x, y);
          matched += 1;
        }
      }
    }
  }

  int FindUnmatchedXValue() const {
    for (int x = 0; x < n; x++) {
      if (x_match[x] == -1) {
        return x;
      }
    }
    assert(false);
  }

  void UpdateLabels(Cost delta, bool* x_in_tree, int* y_parent, Cost* slack) {
    for (int x = 0; x < n; x++) {
      if (x_in_tree[x]) {
        x_label[x] -= delta;
      }
    }
    for (int y = 0; y < n; y++) {
      if (y_parent[y] == -1) {
        slack[y] -= delta;
      } else {
        y_label[y] += delta;
      }
    }
  }

  void RunAugmentationStep()  {
    // An augmentation step consists of searching for a path in the graph of
    // tight edges on which every other edge is included in the matching, but
    // in which the first and last edges are free. Once we find such a path,
    // we can increase the size of our matching by 1 by flipping the matches
    // along it.
    //
    // If we cannot find an augmenting path, this function will change the
    // labels for vertices on slack edges along the path and try again.
    bool* x_in_tree = new bool[n];
    int* y_parent = new int[n];
    for (int x = 0; x < n; x++) {
      x_in_tree[x] = false;
      y_parent[x] = -1;
    }

    int root = FindUnmatchedXValue();
    // slack[y] will be the minimum currently-known slack between y and any
    // node on the left, and slack_x[y] will be the node that minimizes it.
    Cost* slack = new Cost[n];
    int* slack_x = new int[n];
    for (int y = 0; y < n; y++) {
      slack[y] = -GetCost(root, y);
      assert(slack[y] >= 0);
      slack_x[y] = root;
    }
    x_in_tree[root] = true;

    while (true) {
      Cost delta = -1;
      int delta_x, delta_y;
      for (int y = 0; y < n; y++) {
        if (y_parent[y] < 0 && (delta == -1 || slack[y] < delta)) {
          delta = slack[y];
          delta_x = slack_x[y];
          delta_y = y;
        }
      }
      UpdateLabels(delta, x_in_tree, y_parent, slack);
      y_parent[delta_y] = delta_x;
      if (y_match[delta_y] == -1) {
        // Augmenting path found, ending with the edge (delta_x, delta_y).
        // We flip all edges along the path.
        int cur_y = delta_y;
        while (cur_y != -1) {
          int cur_x = y_parent[cur_y];
          int next_y = x_match[cur_x];
          Match(cur_x, cur_y);
          cur_y = next_y;
        }
        matched += 1;
        break;
      }
      // We've added a new node to the BFS tree through only tight edges.
      // We need to adjust slack values as a result.
      int x = y_match[delta_y];
      x_in_tree[x] = true;
      for (int y = 0; y < n; y++) {
        if (y_parent[y] == -1) {
          Cost new_slack = -GetCost(x, y);
          if (slack[y] > new_slack) {
            slack[y] = new_slack;
            slack_x[y] = x;
          }
        }
      }
    }
    delete x_in_tree;
    delete y_parent;
    delete slack;
    delete slack_x;
  }
};

#endif  // __HUNGARIAN__
