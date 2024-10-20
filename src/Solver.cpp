//
// Created by yun dai on 2024/10/19.
//

#include "Solver.h"
//
#include <iostream>
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
} // namespace

namespace sat {
std::ostream &operator<<(std::ostream &out, const BValue &v) {
  switch (v) {

  case B_TRUE:
    return out << "T";
  case B_FASE:
    return out << "F";
  case B_UN_KNOWN:
    return out << "U";
  }
  return out;
}
} // namespace sat

bool Clause::valid() const {

  if (value_.size() < 2) {
    return false;
  }
  for (auto lit : value_) {
    if (!lit.isValid()) {
      return false;
    }
  }
  auto tmp = value_;
  std::sort(tmp.begin(), tmp.end());

  for (size_t i = 1; i < tmp.size(); i++) {
    if (tmp[i - 1] == tmp[i]) {
      return false;
    }
    if (isVarPairLit(tmp[i - 1], tmp[i])) {
      return false;
    }
  }

  return true;
}

bool Solver::add(Lit lit) {
  assert(isInitGood());
  assert(lit.isValid());

  return addClauseImpl({lit});
}

bool Solver::add(Lit f, Lit s) {
  assert(isInitGood());
  assert(f.isValid());
  assert(s.isValid());

  if (f == s) {
    return addClauseImpl({f});
  }
  return addClauseImpl({f, s});
}

bool Solver::add(Lit f, Lit s, Lit t) {
  assert(f.isValid());
  assert(s.isValid());
  assert(t.isValid());

  assert(isInitGood());

  return addClauseImpl({f, s, t});
}
bool Solver::add(std::vector<Lit> lits) {
  assert(isInitGood());
#ifndef NDEBUG
  for (auto lit : lits) {
    assert(lit.isValid());
  }
#endif

  return addClauseImpl(lits);
}

SolverStatus Solver::solve() {
  if (getStatus() != UN_SOLVE) {
    return getStatus();
  }
  auto conf = propagation();

  if (conf != nullptr) {
    return UN_SAT;
  }
  SolverStatus s;

  int number_conf = 1000;
  while (true) {

    if ((s = solveLimit(number_conf)) != UN_SOLVE) {
      solver_status_ = s;
      return s;
    }
    number_conf += 100;
  }
}

SolverStatus Solver::solveLimit(int number_conf) {
  int conf_n = 0;
  Clause *conf = nullptr;

  while (conf_n < number_conf) {
    conf = propagation();
    if (conf) {
      /// analyze
      auto lean = analyze(conf);
      if (lean.second < 0) {
        return UN_SAT;
      }
      cancelUntil(lean.second);
      if (lean.first.size() > 1) {
        auto lean_clause = addClause(lean.first, LEARN);
        ///
        addUnCheckLit(lean.first[0], lean_clause);
      } else {
        assert(0 == lean.second);
        addUnCheckLit(lean.first[0], nullptr);
      }

    } else {
      /// choose decide lit
      auto lit = chooseOneLit();
      if (!lit.isValid()) {
        return SAT;
      }
      decide();
      addUnCheckLit(lit, nullptr);
    }
  }

  return UN_SOLVE;
}

Clause *Solver::propagation() {
  Clause *confl{nullptr};
  while (trail_head_ < trail_.size()) {
    auto lit = trail_[trail_head_++];
    auto neg_lit = ~lit;
    Lit new_watch;
    auto &ws = watch_list_[lit];
    auto it = ws.begin();
    auto jt = ws.begin();

    while (it != ws.end()) {
      auto blocker = it->getBlocker();
      if (getValue(blocker)) {
        *jt++ = *it++;
        continue;
      }

      auto watch_clause = it->getClause();
      it++;

      if (watch_clause->getValue()[0] == neg_lit) {
        watch_clause->getValue()[0] = watch_clause->getValue()[1];
        watch_clause->getValue()[1] = neg_lit;
      }

      assert(watch_clause->getValue()[1] == neg_lit);

      auto first_lit = watch_clause->getValue()[0];

      Watcher w = Watcher(watch_clause, first_lit);

      if (first_lit != blocker && getValue(first_lit)) {
        *jt++ = w;
        continue;
      }

      // [2,...) lit find new water lit
      for (size_t k = 2; k < watch_clause->getValue().size(); k++) {
        if (!isFalse(watch_clause->getValue()[k])) {

          /// remove watch clause watch_clause in lit watch list
          /// add watch_clause in  ~new_watch watch list
          watch_clause->getValue()[1] = watch_clause->getValue()[k];
          watch_clause->getValue()[k] = neg_lit;
          watch_list_[~watch_clause->getValue()[1]].emplace_back(w);
          goto NextClause;
        }
      }
      *jt++ = w;

      if (isFalse(first_lit)) {
        trail_head_ = trail_.size();
        confl = watch_clause;
        while (it != ws.end()) {
          *jt++ = *it++;
        }

      } else {
        addUnCheckLit(first_lit, watch_clause);
      }
    NextClause:;
    }

    ws.resize(jt - ws.begin());
  }

  return confl;
}

std::pair<std::vector<Lit>, int> Solver::analyze(const Clause *conf) {
  assert(conf);
  assert(conf->valid());

  if (getLevel(conf->getValue()[0].getVar()) <= 0) {
    return {{}, -1};
  }

  int pathC = 0;
  Lit p{};
  std::vector<char> seen(max_var_id_ + 1, 0);
  std::vector<Lit> out_learn(1);

  int index = trail_.size() - 1;

  do {
    for (size_t j = (p.isValid() ? 1 : 0); j < conf->getValue().size(); j++) {
      auto q = conf->getValue()[j];
      if (!seen[q.getVar()] && getLevel(q.getVar()) > 0) {
        seen[q.getVar()] = 1;
        if (getLevel(q.getVar()) >= getCurrentLevel()) {
          pathC++;
        } else {
          out_learn.push_back(q);
        }
      }
    }
    while (!seen[trail_[index--].getVar()])
      ;
    p = trail_[index + 1];
    conf = reason_[p.getIndex()];
    seen[p.getVar()] = 0;
    pathC--;
  } while (pathC > 0);
  out_learn[0] = ~p;

  simplifyClause(out_learn);
  int second_high_leval = 0;
  for (size_t i = 1; i < out_learn.size(); i++) {
    if (getLevel(out_learn[i].getVar()) > second_high_leval) {
      second_high_leval = getLevel(out_learn[i].getVar());
    }
  }

  return {out_learn, second_high_leval};
}

Lit Solver::chooseOneLit() {
  while (!var_order_.empty()) {
    auto last = var_order_.back();
    var_order_.pop_back();
    if (value_[last] == B_UN_KNOWN) {
      if (rand() % 2 == 1) {
        return Lit(last, true);
      } else {
        return Lit(last, false);
      }
    }
  }

  return {};
}

void Solver::decide() { trail_limit_.push_back(trail_.size()); }

bool Solver::addClauseImpl(std::vector<Lit> lits, ClauseOrigin origin) {

  if (origin != LEARN) {
    int old_max_id = max_var_id_;
    for (auto lit : lits) {
      if (lit.getVar() > max_var_id_) {
        max_var_id_ = lit.getVar();
      }
    }
    for (auto v = old_max_id == 0 ? 0 : old_max_id + 1; v <= max_var_id_; v++) {
      var_order_.push_back(v);
    }
    if (max_var_id_ > old_max_id && max_var_id_ + 1 > level_.size()) {
      extandVar(1.3 * (max_var_id_ + 1) + 5);
    }
  }

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

  if (1 == lits.size()) {
    addUnCheckLit(level_[0], nullptr);
    return true;
  }

  addClause(lits, origin);

  return true;
}

Clause *Solver::addClause(const std::vector<Lit> &lits, ClauseOrigin origin) {
  assert(lits.size() > 1);

  auto cl = new Clause(lits, origin);
  assert(cl->valid());
  clauses_.push_back(cl);
  Watcher w1(cl, lits[1]);
  Watcher w2(cl, lits[0]);

  watch_list_[~lits[0]].push_back(w1);
  watch_list_[~lits[1]].push_back(w2);
  return cl;
}

// todo
void Solver::cancelUntil(int level) {
  assert(trail_limit_.size() >= level);
  if (trail_limit_.size() == level) {
    return;
  }

  if (level == 0) {
    return;
  }

  for (size_t k = level; k < trail_limit_.size(); k++) {
    var_order_.push_back(trail_[trail_limit_[k]].getVar());
  }

  int loc = trail_limit_[level - 1];

  for (size_t i = trail_.size() - 1; i >= loc; i--) {
    auto lit = trail_[i];
    value_[lit.getVar()] = B_UN_KNOWN;
  }

  trail_limit_.resize(level);

  trail_.resize(loc);
  trail_head_ = trail_.size();
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
      *it = *jt;
      it++;
    }
    jt++;
  }
  lits.resize(it - lits.begin());
  return lits.empty() ? B_FASE : B_UN_KNOWN;
}

void Solver::extandVar(int new_max_num) {
  assert(new_max_num > max_var_id_);

  value_.resize(new_max_num, B_UN_KNOWN);
  level_.resize(new_max_num, -1);
  reason_.resize(2 * new_max_num, nullptr);
}

void Solver::resetStatus() {
  if (solver_status_ != UN_SAT) {
    if (!trail_limit_.empty()) {
      trail_.erase(trail_.begin() + trail_limit_[0], trail_.end());
    }
    trail_limit_.clear();
    solver_status_ = UN_SOLVE;
  }
}

std::vector<BValue> Solver::getModel() const {
  assert(getStatus() == SAT);
  if (getStatus() == SAT) {
    std::vector<BValue> model(getVarNum(), B_UN_KNOWN);
    for (auto &lit : trail_) {
      model[lit.getVar()] = lit.getVarBValue();
    }
    return model;
  }
  return {};
}
