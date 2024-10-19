//
// Created by yun dai on 2024/10/19.
//

#include "Solver.h"
//
#include <gtest/gtest.h>
#include <iostream>

using namespace sat;
using namespace std;
using namespace testing;

TEST(Solver, addClause) {
  Solver solver;
  // x\/ y \/ z
  Lit x(0, false);
  Lit y(1, false);
  Lit z(2, false);
  solver.add(x, y, z);
  /// x \/ ~y

  solver.add(x, ~y);

  ASSERT_EQ(solver.getVarNum(), 3);
  ASSERT_EQ(solver.getClauseNum(), 2);
  ASSERT_EQ(solver.solve(), SAT);

  auto model = solver.getModel();
  for (auto v : model) {
    cout << v << " ";
  }
}
