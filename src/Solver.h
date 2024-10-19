//
// Created by yun dai on 2024/10/19.
//

#ifndef SAT_SRC_SOLVER_H_
#define SAT_SRC_SOLVER_H_
#include <vector>
#include <cassert>
#include <map>

namespace sat {

enum BValue {
  B_TRUE = 0,
  B_FASE,
  B_UN_KNOWN
};

static inline BValue operator~(BValue v) {
  switch (v) {
    case B_TRUE:return B_FASE;
    case B_FASE:return B_TRUE;
    case B_UN_KNOWN:return B_UN_KNOWN;
  }
}

int weakValue(BValue v) {
  return v == B_FASE ? 0 : 1;
}

class Lit {

  int var_{0}; //start from 0
  bool sign_{false};

 public:
  Lit() = default;
  Lit(int v, bool s = false) {
    assert(v >= 0);
    var_ = v;
    sign_ = s;
  }

  int getVar() const {
    return var_;
  }

  bool getSign() const {
    return sign_;
  }
  int getIndex() const {
    return 2 * var_ + (sign_ ? 1 : 0);
  }
  BValue getVarBValue() const {
    return getSign() ? B_FASE : B_TRUE;

  }
  bool operator<(const Lit &other) const {
    return std::pair<int, bool>(var_, sign_) < std::pair<int, bool>(other.var_, other.sign_);
  }
 private:

};

bool operator==(const Lit lhs, const Lit rhs) {
  return lhs.getSign() == rhs.getSign() && lhs.getVar() == rhs.getVar();
}

bool operator!=(const Lit lhs, const Lit rhs) {
  return lhs.getSign() != rhs.getSign() || lhs.getVar() != rhs.getVar();
}

Lit operator~(Lit lit) {
  return Lit(lit.getVar(), !lit.getSign());
}

int weakValue(Lit lit, BValue v) {
  if (lit.getSign()) {
    return v == B_TRUE ? 0 : 1;
  }
  return v == B_FASE ? 0 : 1;
}

enum ClauseOrigin {
  FORMULA = 0,
  LEARN
};

class Clause {

  ClauseOrigin origin_{FORMULA};
  std::vector<Lit> value_;

 public:

  Clause() = default;
  Clause(std::vector<Lit> lits) : value_(std::move(lits)) {

  }

  Clause(std::vector<Lit> lits, ClauseOrigin o) : origin_(o), value_(std::move(lits)) {

  }

  ClauseOrigin getOrigin() const {
    return origin_;
  }

  const std::vector<Lit> &getValue() const {
    return value_;
  }

 private:

};

class Watcher {

  const Clause *clause_{nullptr};

  Lit other_watch_lit_;

 public:
  Watcher() = default;
  Watcher(const Clause *c, Lit other) : clause_(c), other_watch_lit_(other) {

  }
  const Clause *getClause() const {
    return clause_;
  }

  Lit getOther() const {
    return other_watch_lit_;
  }

  bool valid() const {
    return clause_;
  }

 private:

};

enum SolverStatus {
  UN_SOLVE,
  SAT,
  UN_SAT
};

class Solver {

  int max_var_id_{0};

  std::vector<Clause *> clauses_;
  std::map<Lit, std::vector<Watcher> > watch_list_;

  int tail_head_{0};
  std::vector<Lit> tail_;
  std::vector<int> tail_limit_;
  std::vector<BValue> value_;// Var ->
  std::vector<int> level_;// Var ->

  ////Lit index,  Var v  --> 2*v ; ~v--> 2v+1
  // Lit ->
  std::vector<const Clause *> reason_; //lit --> reason cl (cl --> lit)




  SolverStatus solver_status_{UN_SOLVE};

 public:

  bool add(Lit lit);
  bool add(Lit f, Lit s);
  bool add(Lit f, Lit s, Lit t);
  bool add(std::vector<Lit> lits);

  int getVarNum() const {
    return max_var_id_ + 1;
  }

  SolverStatus getStatus() const {
    return solver_status_;
  }

  std::vector<BValue> getModel() const;

  bool isGood() const {
    return getStatus() != UN_SAT;
  }

  void resetStatus();

 private:
  void extandVar(int new_max_num);

  int getCurrentLevel() const {
    return tail_limit_.size();
  }

//// return false iff it find the lits is false
  BValue simplifyForInput(std::vector<Lit> &lits) const;

  void addUnCheckLit(Lit lit, const Clause *cl) {
    tail_.push_back(lit);
    value_[value_[lit.getVar()]] = lit.getVarBValue();
    level_[lit.getVar()] = getCurrentLevel();
    reason_[lit.getIndex()] = cl;
  }

  const Clause *propagation();

  void backToLevel(int level);

  bool isInitGood() const {
    return isGood() && isInitStatus();
  }

  bool isInitStatus() const {
    return tail_limit_.empty();
  }

  bool addClauseImpl(std::vector<Lit> lits, ClauseOrigin origin = FORMULA);

};
}

#endif //SAT_SRC_SOLVER_H_
