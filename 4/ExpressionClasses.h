#ifndef EXPRESSIONCLASSES_H
#define EXPRESSIONCLASSES_H

#include <map>
#include <string>

typedef long long LL;
using namespace std;

LL makeStrHash(const string &s) {
    LL hash = 0;
    LL p = 31;
    for (int i = 0; i < s.length(); i++, p *= 31) {
        hash *= p;
        hash += s[i];
    }
    return hash;
}

struct Expression {
    virtual void initHash() = 0;
    virtual string getOperationCode() = 0;
    virtual LL getOperationHash() {
        return makeStrHash(getOperationCode());
    }
    virtual string getAsString() = 0;
    virtual bool eval(const map<string, bool> &values) = 0;
    virtual int getArity() = 0;
    bool lastValue;
    LL hash;
};

struct Variable : Expression {
    string name;
    Variable(const string &s) {
        name = string(s);
        initHash();
    }

    int getArity() {
        return 0;
    }

    string getOperationCode() {
        return name;
    }

    void initHash() {
        hash = makeStrHash(name);
    }

    string getAsString() {
        return name;
    }

    bool eval(const map<string, bool> &values) {
        auto it = values.find(name);
        if (it != values.end()) {
            lastValue = it->second;
            return lastValue;
        }
    }
};

struct UnaryOperation : Expression {
    Expression *expr;
    bool lastValue1;

    int getArity() {
        return 1;
    }

    UnaryOperation(Expression *expr) {
        this->expr = expr;
    }

    void initHash() {
        hash = expr->hash *31 + getOperationHash();
    }

    string getAsString() {
        return "(" + getOperationCode() + expr->getAsString() + ")";
    }
};

struct BinaryOperation : Expression {
    bool lastValue1;
    bool lastValue2;
    Expression *expr1;
    Expression *expr2;

    int getArity() {
        return 2;
    }

    BinaryOperation(Expression *expr1, Expression *expr2) {
        this->expr1 = expr1;
        this->expr2 = expr2;
    }

    void initHash() {
        hash = expr1->hash * 57 + getOperationHash() * 31 + expr2->hash;
    }

    string getAsString() {
        return "(" + expr1->getAsString() + getOperationCode() + expr2->getAsString() + ")";
    }
};

struct Negation : UnaryOperation {
    Negation(Expression *expr) : UnaryOperation(expr) {}
    string getOperationCode() {
        return "!";
    }

    bool eval(const map<string, bool> &values) {
        lastValue1 = eval(values);
        return lastValue = !lastValue1;
    }
};

struct Implication : BinaryOperation {
    Implication(Expression *expr1, Expression *expr2) : BinaryOperation(expr1, expr2) {
        initHash();
    }
    string getOperationCode() {
        return "->";
    }

    bool eval(const map<string, bool> &values) {
        lastValue1 = expr1->eval(values);
        lastValue2 = expr2->eval(values);
        return lastValue = lastValue1 | !lastValue2;
    }
};

struct Disjunction : BinaryOperation {
    Disjunction(Expression *expr1, Expression *expr2) : BinaryOperation(expr1, expr2) {
        initHash();
    }
    string getOperationCode() {
        return "|";
    }

    bool eval(const map<string, bool> &values) {
        lastValue1 = expr1->eval(values);
        lastValue2 = expr2->eval(values);
        return lastValue = lastValue1 | lastValue2;
    }
};

struct Conjunction : BinaryOperation {
    Conjunction(Expression *expr1, Expression *expr2) : BinaryOperation(expr1, expr2) {
        initHash();
    }
    string getOperationCode() {
        return "&";
    }

    bool eval(const map<string, bool> &values) {
        lastValue1 = expr1->eval(values);
        lastValue2 = expr2->eval(values);
        return lastValue = lastValue1 & lastValue2;
    }
};

bool isVariable(Expression *x) {
    const string &s = x->getOperationCode();
    if (s.length() > 0 && s[0] >= 'A' && s[0] <= 'Z') {
        return true;
    }
    return false;
}

Expression *notX(Expression *x) {
    return new Negation(x);
}

Expression *notNotX(Expression *x) {
    return new Negation(notX(x));
}


bool checkEqualHard(Expression *a, Expression *b) {
    if (!a && !b) return true;
    if (!a || !b) return false;
    if (a->getOperationCode() != b->getOperationCode()) return false;
    if (a->getArity() == 2) {
        BinaryOperation *aa = dynamic_cast<BinaryOperation*>(a);
        BinaryOperation *bb = dynamic_cast<BinaryOperation*>(b);
        if (!checkEqualHard(aa->expr1, bb->expr1)) return false;
        if (!checkEqualHard(aa->expr2, bb->expr2)) return false;
    } else if (a->getArity() == 1) {
        UnaryOperation *aa = dynamic_cast<UnaryOperation*>(a);
        UnaryOperation *bb = dynamic_cast<UnaryOperation*>(b);
        if (!checkEqualHard(aa->expr, bb->expr)) return false;
    }
    return true;
}

// TODO: for 3 Nodes
// a != NULL && b != NULL
bool checkEqual(Expression *a, Expression *b) {
    if (a->hash != b->hash) return false;
    return checkEqualHard(a, b);
}


#endif // EXPRESSIONCLASSES_H
