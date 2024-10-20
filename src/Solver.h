//
// Created by yun dai on 2024/10/19.
//

#ifndef SAT_SRC_SOLVER_H_
#define SAT_SRC_SOLVER_H_
#include <cassert>
#include <iostream>
#include <map>
#include <vector>

namespace sat {

enum BValue { B_TRUE = 0, B_FASE, B_UN_KNOWN };

static inline BValue operator~(BValue v) {
  switch (v) {
  case B_TRUE:
    return B_FASE;
  case B_FASE:
    return B_TRUE;
  case B_UN_KNOWN:
    return B_UN_KNOWN;
  }
}

std::ostream &operator<<(std::ostream &out, const BValue &v);

static inline int weakValue(BValue v) { return v == B_FASE ? 0 : 1; }

class Lit {

  int var_{-1}; // start from 0
  bool sign_{false};

public:
  Lit() = default;
  Lit(int v, bool s = false) {
    assert(v >= 0);
    var_ = v;
    sign_ = s;
  }

  int getVar() const { return var_; }

  bool getSign() const { return sign_; }
  int getIndex() const { return 2 * var_ + (sign_ ? 1 : 0); }
  BValue getVarBValue() const { return getSign() ? B_FASE : B_TRUE; }
  bool isValid() const { return var_ >= 0; }
  bool operator<(const Lit &other) const {
    return std::pair<int, bool>(var_, sign_) <
           std::pair<int, bool>(other.var_, other.sign_);
  }

private:
};

static inline bool operator==(const Lit lhs, const Lit rhs) {
  return lhs.getSign() == rhs.getSign() && lhs.getVar() == rhs.getVar();
}

static inline bool operator!=(const Lit lhs, const Lit rhs) {
  return lhs.getSign() != rhs.getSign() || lhs.getVar() != rhs.getVar();
}

static inline Lit operator~(Lit lit) {
  return Lit(lit.getVar(), !lit.getSign());
}

static inline bool isVarPairLit(Lit lhs, Lit rhs) {
  return lhs.getVar() == rhs.getVar() && (lhs.getSign() != rhs.getSign());
}

static inline int weakValue(Lit lit, BValue v) {
  if (lit.getSign()) {
    return v == B_TRUE ? 0 : 1;
  }
  return v == B_FASE ? 0 : 1;
}

enum ClauseOrigin { FORMULA = 0, LEARN };

class Clause {

  ClauseOrigin origin_{FORMULA};
  std::vector<Lit> value_;

public:
  Clause() = default;
  Clause(std::vector<Lit> lits) : value_(std::move(lits)) {}

  Clause(std::vector<Lit> lits, ClauseOrigin o)
      : origin_(o), value_(std::move(lits)) {}

  ClauseOrigin getOrigin() const { return origin_; }

  const std::vector<Lit> &getValue() const { return value_; }

  std::vector<Lit> &getValue() { return value_; }

  bool valid() const;

private:
};

class Watcher {

  Clause *clause_{nullptr};

  Lit blocker_;

public:
  Watcher() = default;
  Watcher(Clause *c, Lit other) : clause_(c), blocker_(other) {}
  Clause *getClause() const { return clause_; }

  Lit getBlocker() const { return blocker_; }

  bool valid() const { return clause_; }

private:
};

enum SolverStatus { UN_SOLVE, SAT, UN_SAT };

class Solver {

  int max_var_id_{0};

  std::vector<Clause *> clauses_;
  std::map<Lit, std::vector<Watcher>> watch_list_;

  int trail_head_{0};
  std::vector<Lit> trail_;
  std::vector<int> trail_limit_;
  std::vector<BValue> value_; // Var ->
  std::vector<int> level_;    // Var ->
  std::vector<int> var_order_;

  ////Lit index,  Var v  --> 2*v ; ~v--> 2v+1
  // Lit ->
  std::vector<const Clause *> reason_; // lit --> reason cl (cl --> lit)

  SolverStatus solver_status_{UN_SOLVE};

public:
  bool add(Lit lit);
  bool add(Lit f, Lit s);
  bool add(Lit f, Lit s, Lit t);
  bool add(std::vector<Lit> lits);

  int getVarNum() const { return max_var_id_ + 1; }

  int getClauseNum() const { return clauses_.size(); }

  SolverStatus solve();

  std::vector<BValue> getModel() const;

  SolverStatus getStatus() const { return solver_status_; }

  bool isGood() const { return getStatus() != UN_SAT; }

  void resetStatus();

private:
  SolverStatus solveLimit(int number_conf);

  void extandVar(int new_max_num);

  int getCurrentLevel() const { return trail_limit_.size(); }

  //// return false iff it find the lits is false
  BValue simplifyForInput(std::vector<Lit> &lits) const;

  void addUnCheckLit(Lit lit, const Clause *cl) {
    trail_.push_back(lit);
    value_[value_[lit.getVar()]] = lit.getVarBValue();
    level_[lit.getVar()] = getCurrentLevel();
    reason_[lit.getIndex()] = cl;
  }

  Clause *propagation();

  std::pair<std::vector<Lit>, int> analyze(const Clause *conf);

  Lit chooseOneLit();

  void decide();

  void cancelUntil(int level);

  BValue getBValue(int v) const { return value_[v]; }

  bool isFalse(Lit lit) const {
    if (lit.getSign()) {
      return value_[lit.getVar()] == B_TRUE;
    }
    return value_[lit.getVar()] == B_FASE;
  }

  bool getValue(Lit lit) const {
    return value_[lit.getVar()] == lit.getVarBValue();
  }

  int getLevel(int v) const { return level_[v]; }

  bool isInitGood() const { return isGood() && isInitStatus(); }

  bool isInitStatus() const { return trail_limit_.empty(); }
  bool addClauseImpl(std::vector<Lit> lits, ClauseOrigin origin = FORMULA);

  Clause *addClause(const std::vector<Lit> &lits, ClauseOrigin origin);
};
} // namespace sat

#endif // SAT_SRC_SOLVER_H_
