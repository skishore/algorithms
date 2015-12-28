// Written in 2015 by Shaunak Kishore (kshaunak@gmail.com).
//
// To the extent possible under law, the author(s) have dedicated all copyright
// and related and neighboring rights to this software to the public domain
// worldwide. This software is distributed without any warranty.
//
// Implementation of the Hungarian algorithm for finding minimum-weight
// matchings. Usage:
//  - Compute Cost** cost_matrix, an nxn array where cost_matrix[x][y]
//    is the cost of matching x with y.
//  - Construct Hungarian(n, cost_matrix).
//  - Call Solve() on the Hungarian instance and verify that its status is OK.
//  - Use GetTotalCost, GetXMatch, and GetYMatch to read the output.
//
// The algorithm will minimize the total cost of the matching by default.
// If you pass maximize=true in the constructor, it will maximize the total
// cost instead.
//
// Costs in the cost matrix may be arbitrary integers. The first step of the
// algorithm is to reduce the matrix so that all costs are non-negative, but
// but this is handled entirely within the solver.
//
// We restrict to integer costs because the algorithm is not numerically stable.
// When all inputs are integers, the intermediate edge weights we compute are
// also guaranteed to be integers.

#ifndef __HUNGARIAN__
#define __HUNGARIAN__

typedef int Cost;

namespace {
inline Cost min(Cost a, Cost b) {
  return (a < b ? a : b);
}
}  // namespace

class Hungarian {
 public:
  // cost_matrix must be an nxn matrix of Cost values. However, templating this
  // contstructor allows it to take both Cost** and vector<vector<Cost>>,
  // without actually including the std::vector library.
  template <typename T>
  Hungarian(int n_, const T& cost_matrix_, bool maximize=false)
      : n(n_), cost_matrix(new Cost[n*n]), x_match(new int[n]),
        y_match(new int[n]), x_label(new Cost[n]), y_label(new Cost[n]) {
    const int sign = (maximize ? -1 : 1);
    for (int x = 0; x < n; x++) {
      for (int y = 0; y < n; y++) {
        cost_matrix[n*x+y] = sign*cost_matrix_[x][y];
      }
    }
  }

  enum Status {
    OK = 0,
    ERROR_INTEGER_OVERFLOW = 1,
    ERROR_AUGMENTATION_STEP_FAILED = 2,
    ERROR_NON_TIGHT_EDGE_MATCHED = 3
  };

  Status Solve() {
    for (int i = 0; i < n; i++) {
      // Initially, all vertices are unmatched.
      x_match[i] = -1;
      y_match[i] = -1;
    }
    matched = 0;
    // We first reduce the matrix so that all entries are non-negative.
    // This step may fail. In particular, it will fail if there are two entries
    // in the cost matrix that are more than INT_MAX apart.
    if (!ReduceCostMatrix()) {
      return ERROR_INTEGER_OVERFLOW;
    }
    // Greedily match pairs vertices that are connected by a tight edge.
    // This step will help the algorithm terminate in fewer than n augmentation
    // steps on easier inputs.
    FindGreedySolution();
    // Run augmentation steps to finish matching the vertices.
    while (matched < n) {
      const int last_matched = matched;
      RunAugmentationStep();
      if (matched <= last_matched) {
        return ERROR_AUGMENTATION_STEP_FAILED;
      }
      for (int x = 0; x < n; x++) {
        if (x_match[x] != -1 && GetSlack(x, x_match[x]) != 0) {
          return ERROR_NON_TIGHT_EDGE_MATCHED;
        }
      }
    }
    return OK;
  }

  ~Hungarian() {
    delete[] cost_matrix;
    delete[] x_match;
    delete[] y_match;
    delete[] x_label;
    delete[] y_label;
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
  // We define the slack of the edge (x, y) to be:
  //   slack(x, y) = cost_matrix[n*x+y] - x_label[x] - y_label[y]
  // An edge is tight if its slack is zero. Throughout this algorithm, we will
  // maintain the invariant that all matched edges are tight.
  Cost* x_label;
  Cost* y_label;

  // The number of edges currently matched.
  int matched;

  Cost GetSlack(int x, int y) const {
    return cost_matrix[n*x+y] - x_label[x] - y_label[y];
  }

  void Match(int x, int y) {
    x_match[x] = y;
    y_match[y] = x;
  }

  bool ReduceCostMatrix() {
    // Subtract the minimum value in each column from all entries in that column.
    // After this operation, all entries in the matrix will be non-negative, so
    // x-labels of 0 will satisfy the slack inequality.
    //
    // Returns false if a value in the matrix is still negative after reduction,
    // which can only occur due to integer underflow.
    for (int x = 0; x < n; x++) {
      Cost min_cost = 0;
      for (int y = 0; y < n; y++) {
        min_cost = min(min_cost, cost_matrix[n*x+y]);
      }
      for (int y = 0; y < n; y++) {
        cost_matrix[n*x+y] -= min_cost;
      }
      x_label[x] = 0;
    }
    // Do the same for y.
    for (int y = 0; y < n; y++) {
      Cost min_cost = 0;
      for (int x = 0; x < n; x++) {
        min_cost = min(min_cost, cost_matrix[n*x+y]);
      }
      for (int x = 0; x < n; x++) {
        cost_matrix[n*x+y] -= min_cost;
        if (cost_matrix[n*x+y] < 0) {
          return false;
        }
      }
      y_label[y] = 0;
    }
    return true;
  }

  void FindGreedySolution() {
    for (int x = 0; x < n; x++) {
      for (int y = 0; y < n; y++) {
        if (x_match[x] == -1 && y_match[y] == -1 && GetSlack(x, y) == 0) {
          Match(x, y);
          matched += 1;
        }
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
    if (root == -1) {
      // All x-values are matched. Return early. This should not occur normally;
      // RunAugmentationStep should only be called if there are unmatched nodes.
      return;
    }

    // slack[y] will be the minimum currently-known slack between y and any
    // node on the left, and slack_x[y] will be the node that minimizes it.
    Cost* slack = new Cost[n];
    int* slack_x = new int[n];
    for (int y = 0; y < n; y++) {
      slack[y] = GetSlack(root, y);
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
          Cost new_slack = GetSlack(x, y);
          if (slack[y] > new_slack) {
            slack[y] = new_slack;
            slack_x[y] = x;
          }
        }
      }
    }
    delete[] x_in_tree;
    delete[] y_parent;
    delete[] slack;
    delete[] slack_x;
  }

  int FindUnmatchedXValue() const {
    for (int x = 0; x < n; x++) {
      if (x_match[x] == -1) {
        return x;
      }
    }
    // We should NEVER reach this point while running the algorithm.
    // If all x-values are matched, we should not be in an augmentation step.
    //assert(false);
    return -1;
  }

  void UpdateLabels(Cost delta, bool* x_in_tree, int* y_parent, Cost* slack) {
    for (int x = 0; x < n; x++) {
      if (x_in_tree[x]) {
        x_label[x] += delta;
      }
    }
    for (int y = 0; y < n; y++) {
      if (y_parent[y] == -1) {
        slack[y] -= delta;
      } else {
        y_label[y] -= delta;
      }
    }
  }
};

#endif  // __HUNGARIAN__
