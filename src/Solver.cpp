//
// Created by yun dai on 2024/10/19.
//


#include "Solver.h"

using namespace std;
using namespace sat;

namespace {
BValue simplifyClause(std::vector<Lit> &lits) {

  std::sort(lits.begin(), lits.end());
  auto it = std::unique(lits.begin(), lits.end());
  lits.resize(it - lits.begin());

  if (lits.size() < 2) {
    return B_UN_KNOWN;
  }

  it = lits.begin();
  auto jt = lits.begin() + 1;
  while (jt != lits.end()) {

    if (*it != *jt) {
      if (it->getVar() == jt->getVar()) {
        lits.clear();
        return B_TRUE;
      }
      it++;
      *it = *jt;
    }
    jt++;
  }
  it++;
  lits.resize(it - lits.begin());

  if (lits.empty()) {
    return B_FASE;
  }

  return B_UN_KNOWN;

}
}

bool Solver::add(Lit lit) {
  assert(isInitGood());

  return addClauseImpl({lit});
}

bool Solver::add(Lit f, Lit s) {
  assert(isInitGood());

  if (f == s) {
    return addClauseImpl({f});
  }
  return addClauseImpl({f, s});

}

bool Solver::add(Lit f, Lit s, Lit t) {

  assert(isInitGood());

  return addClauseImpl({f, s, t});

}
bool Solver::add(std::vector<Lit> lits) {
  assert(isInitGood());

  return addClauseImpl(lits);
}

bool Solver::addClauseImpl(std::vector<Lit> lits, ClauseOrigin origin) {

  if (origin == FORMULA) {
    auto s = simplifyForInput(lits);
    if (s != B_UN_KNOWN) {
      return s;
    }
  }

  if (lits.empty()) {
    solver_status_ = UN_SAT;
    return false;
  }

  if (origin != LEARN) {

    int old_max_id = max_var_id_;
    for (auto lit : lits) {
      if (lit.getVar() > max_var_id_) {
        max_var_id_ = lit.getVar();
      }
    }
    if (max_var_id_ > old_max_id) {
      extandVar(1.3 * (max_var_id_ + 1) + 5);
    }
  }
  if (1 == lits.size()) {
    addUnCheckLit(level_[0], nullptr);
    return true;
  }

  auto cl = new Clause(lits, origin);
  clauses_.push_back(cl);
  Watcher w1(cl, lits[1]);
  Watcher w2(cl, lits[0]);

  watch_list_[~lits[0]].push_back(w1);
  watch_list_[~lits[1]].push_back(w2);

  return true;

}
//// return false iff it find the lits is false
BValue Solver::simplifyForInput(std::vector<Lit> &lits) const {
  assert(isInitGood());

  if (simplifyClause(lits) == B_TRUE) {
    return B_TRUE;
  }

  auto it = lits.begin();
  auto jt = lits.begin();
  while (jt != lits.end()) {
    if (value_[jt->getVar()] == jt->getVarBValue()) {
      lits.clear();
      return B_TRUE;
    } else if (value_[jt->getVar()] != (~(jt->getVarBValue()))) {
      it++;
      *it = *it;
    }
    jt++;
  }
  it++;
  lits.resize(it - lits.begin());
  return lits.empty() ? B_FASE : B_UN_KNOWN;

}

void Solver::extandVar(int new_max_num) {
  assert(new_max_num > max_var_id_);
  max_var_id_ = new_max_num - 1;
  value_.resize(new_max_num, B_UN_KNOWN);
  level_.resize(new_max_num, -1);
  reason_.resize(2 * new_max_num, nullptr);
}

void Solver::resetStatus() {
  if (solver_status_ != UN_SAT) {
    if (!tail_limit_.empty()) {
      tail_.erase(tail_.begin() + tail_limit_[0], tail_.end());
    }
    tail_limit_.clear();

    solver_status_ = UN_SOLVE;
  }
}

std::vector<BValue> Solver::getModel() const {
  assert(getStatus() == SAT);
  if (getStatus() == SAT) {
    std::vector<BValue> model(getVarNum(), B_UN_KNOWN);
    for (auto &lit : tail_) {
      model[lit.getVar()] = lit.getVarBValue();
    }
    return model;
  }
  return {};

}

