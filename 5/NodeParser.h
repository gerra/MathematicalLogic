#ifndef NODEPARSER_H
#define NODEPARSER_H

#include <map>
#include <string>
#include <vector>
#include <set>
#include <iostream>

using namespace std;

const int N = 5000;

int count = 0;
long long prime[N * N];

string getStringWithoutSpaces(const string & s) {
    string res = "";
    for (unsigned int i = 0; i < s.length(); i++) {
        char c = s[i];
        if (!isspace(c)) res += c;
    }
    return res;
}

struct Node {
    bool hasKvantors;
    bool isPredvar;
    long long hash;
    int vertCnt;
    int ptrCnt;
    bool lastValue;
    vector<Node*> terms;
    string s;
    Node * l;
    Node * r;
    Node() : vertCnt(0), ptrCnt(0), l(NULL), r(NULL) {}
    Node(string s, Node * l, Node * r) : s(s), l(l), r(r) {
        if (s == "?" || s == "@") {
            hasKvantors = true;
            isPredvar = r->isPredvar;
        } else {
            hasKvantors = (l ? l->hasKvantors : false) | (r ? r->hasKvantors : false);
            isPredvar = !(l ? l->hasKvantors : false) & !(r ? r->hasKvantors : false);
        }
        //if (isPredvar) cout << getAsString() << "\n";
        //cout << s << "\n";
        vertCnt = 1;
        ptrCnt = 0;
        int lCnt = 0, rCnt = 0;
        if (l) {
            lCnt  = l->vertCnt;
            vertCnt += lCnt;
            l->ptrCnt++;
        }
        if (r) {
            rCnt  = r->vertCnt;
            vertCnt += rCnt;
        }
        hash = 0;
        if (l) hash += l->hash;
        for (int i = 0; i < s.length(); i++) {
            hash *= prime[1];
            hash += s[i];
        }
        if (r) {
            hash *= prime[rCnt];
            hash += r->hash;
            r->ptrCnt++;
        }

    }
    Node(string s, vector<Node*> &terms) : Node(s, NULL, NULL) {
        this->terms = terms;
        hash = terms[0]->hash;
        for (int i = 1; i < terms.size(); i++) {
            hash *= prime[terms[i]->vertCnt];
            hash += terms[i]->hash;
        }
        for (int i = 0; i < s.length(); i++) {
            hash *= prime[1];
            hash += s[i];
        }
    }

    ~Node() {
        if (l && l->ptrCnt == 0) delete l;
        if (r && r->ptrCnt == 0) delete r;
    }

    string getAsString(bool isMain = true) {
        string result = "";
        bool isInc = false;
        if (s[0] == '\'' && (l->s[0] == '\'' || !l->l && !l->r)) {
            isInc = true;
        }
        if (!isVariable() && !isMain && !isInc && !isNil()) {
            result += "(";
        }
        if (s != "@" && s != "?") {
            if (l) {
                result += l->getAsString(false);
            }
            result += s;
        } else {
            result += s;
            if (l) {
                result += l->getAsString(false);
            }
        }
        if (r) {
            result += r->getAsString(false);
        }
        if (terms.size() != 0) {
            result += "(";
            for (int i = 0; i < terms.size() - 1; i++) {
                result += terms[i]->getAsString() + ",";
            }
            result += terms.back()->getAsString();
            result += ")";
        }
        if (!isVariable() && !isMain && !isInc && !isNil()) {
            result += ")";
        }
        return result;
    }

    bool isNil() {
        return s.length() == 1 && s[0] == '0';
    }

    bool isVariable() {
        if (s.length() > 0 && s[0] >= 'a' && s[0] <= 'z' && terms.size() == 0) {
            return true;
        }
        return false;
    }

    bool isFunction() {
        if (s.length() > 0 &&
            (
                    (s[0] >= 'a' && s[0] <= 'z' && terms.size() != 0) ||
                    s[0] == '\'' || s[0] == '*' || s[0] == '+' || s[0] == '0'
            )) {
            return true;
        }
        return false;
    }

    bool isPredicate() {
        if (s.length() > 0 && s[0] >= 'A' && s[0] <= 'Z') {
            return true;
        }
        return false;
    }

    void getVars(set<string> &vars) {
        if (isPredicate()) {
            vars.insert(s);
            return;
        }
        if (l) l->getVars(vars);
        if (r) r->getVars(vars);
    }

    set<string> getVars() {
        set<string> vars;
        getVars(vars);
        return vars;
    }
};

Node *NIL;
Node *A;
Node *CONST;

struct SubstituteError {
    Node *x, *y;
    string a;
    // y[a:=x]
    SubstituteError(Node *y, const string &a, Node *x) : x(x), y(y), a(a) {}
};

struct VariableFreeError {
    Node *x;
    string a;
    VariableFreeError(Node *x, const string &a) : x(x), a(a) {}
};

struct KvantorError {
    string type;
    string a;
    Node *x;
    KvantorError(const string &type, const string &a, Node *x) : type(type), a(a), x(x) {}
};

struct UnknownError {

};

Node *notX(Node *x) {
    return new Node("!", NULL, x);
}

Node *notNotX(Node *x) {
    return notX(notX(x));
}

vector<Node*> axioms;

bool checkEqual(Node * a, Node * b) {
    if (!a && !b) return true;
    if (!a || !b) return false;
    if (a == b) return true;
    if (a->hash != b->hash) return false;
    else return true;
    if (a->terms.size() != b->terms.size()) return false;
    if (a->s != b->s) return false;
    for (int i = 0; i < a->terms.size(); i++) {
        if (!checkEqual(a->terms[i], b->terms[i])) {
            return false;
        }
    }
    if (!checkEqual(a->l, b->l)) return false;
    if (!checkEqual(a->r, b->r)) return false;
    return true;
}




Node *parseExpression(const string &s, int &ptr);
Node *parseDisjuction(const string &s, int &ptr);
Node *parseConjuction(const string &s, int &ptr);
Node *parseUnary(const string &s, int &ptr);
Node *parsePredicate(const string &s, int &ptr);
Node *parseTerm(const string &s, int &ptr);
Node *parseSummand(const string &s, int &ptr);
Node *parseMultiplied(const string &s, int &ptr);
Node *parseLowLevelMultiplied(const string &s, int &ptr);
void getAA(Node *a, vector<Node*> &proof);

Node * parseLowLevelMultiplied(const string &s, int &ptr) {
    if (ptr >= s.length()) return NULL;
    char c = s[ptr];
    if (c >= 'a' && c <= 'z') {
        string name;
        name += c;
        ptr++;
        while (ptr < s.length() && s[ptr] >= '0' && s[ptr] <= '9') {
            name += s[ptr++];
        }
        if (ptr < s.length() && s[ptr] == '(')  {
            ptr++;
            vector<Node*> terms;
            terms.push_back(parseTerm(s, ptr));
            while (ptr < s.length() && s[ptr] == ',') {
                ptr++;
                terms.push_back(parseTerm(s, ptr));
            }
            if (ptr == s.length() || s[ptr++] != ')') throw ") after function end expected";
            return new Node(name, terms);
        } else {
            return new Node(name, NULL, NULL);
        }
    } else if (c == '(') {
        ptr++;
        Node *res = parseTerm(s, ptr);
        if (ptr == s.length() || s[ptr++] != ')') throw ") in parseMultiplied expected";
        return res;
    } else if (c == '0') {
        ptr++;
        return new Node("0", NULL, NULL);
    }
    throw "Incorrect multiplied";
}

Node * parseMultiplied(const string &s, int &ptr) {
    Node *res = parseLowLevelMultiplied(s, ptr);
    while (ptr < s.length() && s[ptr] == '\'') {
        res = new Node("'", res, NULL);
        ptr++;
    }
    return res;
}

Node * parseSummand(const string &s, int &ptr) {
    Node * expr = parseMultiplied(s, ptr);
    while (ptr < s.length() && s[ptr] == '*') {
        ptr++;
        Node * expr2 = parseMultiplied(s, ptr);
        expr = new Node("*", expr, expr2);
    }
    return expr;
}

Node * parseTerm(const string &s, int &ptr) {
    Node * expr = parseSummand(s, ptr);
    while (ptr < s.length() && s[ptr] == '+') {
        ptr++;
        Node * expr2 = parseSummand(s, ptr);
        expr = new Node("+", expr, expr2);
    }
    return expr;
}

Node * parsePredicate(const string &s, int &ptr) {
    if (ptr >= s.length()) return NULL;
    char c = s[ptr];
    if (c >= 'A' && c <= 'Z') {
        string name;
        name += c;
        ptr++;
        while (ptr < s.length() && s[ptr] >= '0' && s[ptr] <= '9') {
            name += s[ptr++];
        }

        if (ptr == s.length() || s[ptr] != '(') {
            return new Node(name, NULL, NULL);
        }
        ptr++;
        vector<Node*> terms;
        terms.push_back(parseTerm(s, ptr));
        while (ptr < s.length() && s[ptr] == ',') {
            ptr++;
            terms.push_back(parseTerm(s, ptr));
        }
        if (ptr == s.length() || s[ptr++] != ')') throw ") after predicate end expected";
        return new Node(name, terms);
    } else {
        Node *term1 = parseTerm(s, ptr);
        if (s[ptr++] != '=') throw "= in predicate expected";
        Node *term2 = parseTerm(s, ptr);
        return new Node("=", term1, term2);
    }
}

Node * parseUnary(const string &s, int &ptr) {
    if (ptr >= s.length()) return NULL;
    const char c = s[ptr];
    const int fPtr = ptr;

    Node *v1 = NULL;
    try {
        if (c == '@' || c == '?') {
            ptr++;
            if (s[ptr] < 'a' || s[ptr] > 'z') {
                throw string("a...z after ") + c + string(" expected");
            }
            string name;
            name += s[ptr++]; // >= 'a' and <= 'z'
            while (ptr < s.length() && s[ptr] >= '0' && s[ptr] <= '9') {
                name += s[ptr++];
            }
            v1 = new Node(c == '?' ? "?" : "@", new Node(name, NULL, NULL), parseUnary(s, ptr));
        }
    } catch(...) {
        v1 = NULL;
    }
    if (v1) {
        return v1;
    }

    ptr = fPtr;
    try {
        if (c == '!') {
            ptr++;
            Node *expr = parseUnary(s, ptr);
            v1 = notX(expr);
        }
    } catch(...) {
        v1 = NULL;
    }
    if (v1) {
        return v1;
    }

    ptr = fPtr;
    try {
        if (c == '(') {
            ptr++;
            Node * expr = parseExpression(s, ptr);
            if (ptr >= s.length() || s[ptr++] != ')') {
                throw ") doesn't exist";
            }
            return expr;
        }
    } catch(...) {
        v1 = NULL;
    }
    if (v1) {
        return v1;
    }

    ptr = fPtr;
    return parsePredicate(s, ptr);

}

Node * parseConjuction(const string &s, int &ptr) {
    Node * expr = parseUnary(s, ptr);
    while (ptr < s.length() && s[ptr] == '&') {
        ptr++;
        Node * expr2 = parseUnary(s, ptr);
        expr = new Node("&", expr, expr2);
    }
    return expr;
}

Node * parseDisjuction(const string &s, int &ptr) {
    Node * expr = parseConjuction(s, ptr);
    while (ptr < s.length() && s[ptr] == '|') {
        ptr++;
        Node * expr2 = parseConjuction(s, ptr);
        expr = new Node("|", expr, expr2);
    }
    return expr;
}

Node * parseExpression(const string &s, int &ptr) {
    Node * expr1 = parseDisjuction(s, ptr);
    if (ptr < s.length() && s[ptr] == '-' && s[++ptr] == '>') {
        ptr++;
        Node * expr2 = parseExpression(s, ptr);
        return new Node("->", expr1, expr2);
    }
    return expr1;
}

Node * parseStringToFormula(const string &s) {
    int ptr = 0;
    string ss = getStringWithoutSpaces(s);
    return parseExpression(ss, ptr);
}


// by predicate or by variable
bool fillMap(Node * formula, Node * template_, map<string, vector<Node *> > &variableMap, bool byPred = true) {
    if (!formula && !template_) return true;
    if (!formula || !template_) return false;
    const string &tempStr = template_->s;
    if (byPred && template_->isPredicate() || !byPred && template_->isVariable()) {
        variableMap[tempStr].push_back(formula);
        return true;
    } else {
        if (tempStr != formula->s) {
            return false;
        }
        return fillMap(formula->l, template_->l, variableMap, byPred) &&
               fillMap(formula->r, template_->r, variableMap, byPred);
    }
}

// by predicate or by variable
bool checkFormulaIsSimilarToTemplate(Node *formula, Node *template_, bool byPred = true) {
    if (!formula && !template_) return true;
    if (!formula || !template_) return false;
    if (formula == template_) return true;
    map<string, vector<Node*> > variableMap;
    if (fillMap(formula, template_, variableMap, byPred)) {
        for (auto& it : variableMap) {
            vector<Node*> &nodes = it.second;
            for (Node* node : nodes) {
                if (!checkEqual(node, *nodes.begin())) {
                    return false;
                }
            }
        }
        return true;
    }
    return false;
}

// for 11, 12, 21 axioms
bool checkFormulaIsSimilarToTemplate2(Node *formula, Node *template_) {
    if (!formula && !template_) return true;
    if (!formula || !template_) return false;
    if (formula == template_) return true;
    if (template_->isVariable()) {
        return formula->isVariable();
    }
    if (template_->isPredicate()) {
        return true;
    }
    if (formula->s != template_->s) {
        return false;
    }
    return checkFormulaIsSimilarToTemplate2(formula->l, template_->l) &&
           checkFormulaIsSimilarToTemplate2(formula->r, template_->r);
}

Node *getFirstNotBound(Node *formula, Node *template_, const string &x) {
    if (!formula || !template_) return NULL;
    if (template_->s == x) {
        return formula;
    }

    if (template_->s != formula->s) {
        return NULL;
    }

    if (template_->terms.size() != formula->terms.size()) {
        return NULL;
    }

    bool isKvant = false;
    if (formula->s == "@" || formula->s == "?") {
        if (formula->l->s == x) {
            return NULL;
        }
        isKvant = true;
    }

    for (int i = 0; i < formula->terms.size(); i++) {
        Node *res = getFirstNotBound(formula->terms[i],
                                     template_->terms[i],
                                     x);
        if (res) return res;
    }

    if (!isKvant) {
        Node *res1 = getFirstNotBound(formula->l, template_->l, x);
        if (res1) return res1;
    }
    Node *res2 = getFirstNotBound(formula->r, template_->r, x);
    if (res2) return res2;
}

bool checkIsFreeForSub(Node *v, const map<string, int> &bounded) {
    if (!v) return true;
    for (Node *term : v->terms) {
        if  (!checkIsFreeForSub(term, bounded)) {
            return false;
        }
    }
    if (v->isVariable()) {
        auto it = bounded.find(v->s);
        return it == bounded.end() || it->second == 0;
    }
    return checkIsFreeForSub(v->l, bounded) && checkIsFreeForSub(v->r, bounded);
}

bool checkIsNotFree(Node *v, const string &x, map<string, int> &bounded) {
    if (!v) return true;
    if (v->s == "@" || v->s == "?") {
        bounded[v->l->s]++;
    }

    if (v->isVariable()) {
        auto it = bounded.find(v->s);
        return it == bounded.end() || it->second != 0;
    }
    bool result = checkIsNotFree(v->l, x, bounded) && checkIsNotFree(v->r, x, bounded);
    if (v->s == "@" || v->s == "?") {
        bounded[v->l->s]--;
    }
    return result;
}

bool checkIsNotFree(Node *v, const string &x) {
    map<string, int> bounded;
    return checkIsNotFree(v, x, bounded);
}

Node *substitute(Node *alpha, const string &x, Node *tetta, map<string, int> &bounded, bool &isFree) {
    if (!alpha) return NULL;

    bool isKvant = false;
    if (alpha->s == "@" || alpha->s == "?") {
        if (alpha->l->s == x) {
            return alpha;
        }
        bounded[alpha->l->s]++;
        isKvant = true;
        return new Node(alpha->s,
                        alpha->l,
                        substitute(alpha->r, x, tetta, bounded, isFree));
    }
    Node *result = NULL;
    if (alpha->s == x) {
        if (!checkIsFreeForSub(tetta, bounded)) {
            isFree = false;
        }
        result = tetta;
    } else {
        if (alpha->terms.size() == 0) {
            result = new Node(alpha->s,
                              substitute(alpha->l, x, tetta, bounded, isFree),
                              substitute(alpha->r, x, tetta, bounded, isFree));
        } else {
            vector<Node*> terms;
            for (Node *term : alpha->terms) {
                terms.push_back(substitute(term, x, tetta, bounded, isFree));
            }
            result = new Node(alpha->s, terms);
        }
    }
    if (isKvant) {
        bounded[alpha->l->s]--;
    }
    return result;
}

// alpha[x:=tetta]
Node *substitute(Node *alpha, const string &x, Node *tetta, bool &isFree) {
    map<string, int> bounded;
    Node *result = substitute(alpha, x, tetta, bounded, isFree);
    return result;
}

Node *substitute(Node *alpha, const string &x, Node *tetta) {
    bool isFree = true;
    return substitute(alpha, x, tetta, isFree);
}

Node *getFormulaFromTemplate(Node *v, Node *a = NULL, Node *b = NULL, Node *c = NULL) {
    if (!v) return NULL;
    if (v->s == "A") return a;
    if (v->s == "B") return b;
    if (v->s == "C") return c;
    return new Node(v->s,
                    getFormulaFromTemplate(v->l, a, b, c),
                    getFormulaFromTemplate(v->r, a, b, c));
}

Node *getAxiom(int, Node *a = NULL, Node *b = NULL, Node *c = NULL);

void init() {
    prime[0] = 1;
    prime[1] = 31;
    for (int i = 2; i < N * N; i++) {
        prime[i] = prime[i - 1] * prime[1];
    }
    axioms = vector<Node*>(30);
    axioms[1] = parseStringToFormula("A->B->A");
    axioms[2] = parseStringToFormula("(A->B)->(A->B->C)->(A->C)");
    axioms[3] = parseStringToFormula("A->B->A&B");
    axioms[4] = parseStringToFormula("A&B->A");
    axioms[5] = parseStringToFormula("A&B->B");
    axioms[6] = parseStringToFormula("A->A|B");
    axioms[7] = parseStringToFormula("B->A|B");
    axioms[8] = parseStringToFormula("(A->C)->(B->C)->(A|B->C)");
    axioms[9] = parseStringToFormula("(A->B)->(A->!B)->!A");
    axioms[10] = parseStringToFormula("!!A->A");

    axioms[11] = parseStringToFormula("@xA->A(x)");
    axioms[12] = parseStringToFormula("A(x)->?xA");

    axioms[13] = parseStringToFormula("a=b->a'=b'");
    axioms[14] = parseStringToFormula("a=b->a=c->b=c");
    axioms[15] = parseStringToFormula("a'=b'->a=b");
    axioms[16] = parseStringToFormula("!a'=0");
    axioms[17] = parseStringToFormula("a+b'=(a+b)'");
    axioms[18] = parseStringToFormula("a+0=a");
    axioms[19] = parseStringToFormula("a*0=0");
    axioms[20] = parseStringToFormula("a*b'=a*b+a");
    axioms[21] = parseStringToFormula("A(x)&@x(A->A(x))->A");

    NIL = new Node("0", NULL, NULL);
    A = new Node("a", NULL, NULL);
    Node *tmp = new Node("=", NIL, NIL);
    CONST = getAxiom(1, tmp, tmp);
}

int checkIsAxiom(Node *formula) {
    for (int i = 1; i <= 10; i++) {
        if (checkFormulaIsSimilarToTemplate(formula, axioms[i])) {
            return i;
        }
    }
    if (checkFormulaIsSimilarToTemplate2(formula, axioms[11])) {
        Node *x = getFirstNotBound(formula->r,
                                   formula->l->r,
                                   formula->l->l->s);
        //cout << x << "\n";
        if (x) {
            bool isFree = true;
            Node *sub = substitute(formula->l->r,
                                   formula->l->l->s,
                                   x, isFree);
            if (checkEqual(sub, formula->r)) {
                if (isFree) {
                    return 11;
                } else {
                    throw SubstituteError(formula->l->r,
                                          formula->l->l->s,
                                          x);
                }
            }
        } else {
            if (checkEqual(formula->l->r, formula->r)) return 11;
        }
    }
    if (checkFormulaIsSimilarToTemplate2(formula, axioms[12])) {
        Node *x = getFirstNotBound(formula->l,
                                   formula->r->r,
                                   formula->r->l->s);
        if (x) {
            bool isFree = true;
            Node *sub = substitute(formula->r->r,
                                   formula->r->l->s,
                                   x, isFree);
            if (checkEqual(sub, formula->l)) {
                if (isFree) {
                    return 12;
                } else {
                    throw SubstituteError(formula->r->r,
                                          formula->r->l->s,
                                          x);
                }
            }
        } else {
            if (checkEqual(formula->r->r, formula->l)) return 12;
        }
    }

    for (int i = 13; i <= 20; i++) {
        //if (checkFormulaIsSimilarToTemplate(formula, axioms[i], false)) {
        if (checkEqual(formula, axioms[i])) {
            return i;
        }
    }
    if (checkFormulaIsSimilarToTemplate2(formula, axioms[21])) {
        if (checkEqual(formula->r, formula->l->r->r->l)) {
            const string &x = formula->l->r->l->s;
            bool isFree = true;
            Node *sub0 = substitute(formula->r, x, new Node("0", NULL, NULL), isFree);
            if (checkEqual(sub0, formula->l->l)) {
                Node *subx = substitute(formula->r, x, new Node("\'", new Node(x, NULL, NULL), NULL), isFree);
                if (checkEqual(subx, formula->l->r->r->r)) {
                    return 21;
                }
            }
        }
    }

    return -1;
}

bool checkForallRule(Node *v, const vector<Node*> &formulas) {
    if (v->s == "->" && v->r->s == "@") {
        Node *toFind = new Node("->", v->l, v->r->r);
        /* if (checkIsNotFree(v->l, v->r->l->s)) {
             for (Node *formula : formulas) {
                 if (checkEqual(toFind, formula)) {
                     return true;
                 }
             }
         } else {
             throw VariableFreeError(v->l, v->r->l->s);
         }*/
        for (Node *formula : formulas) {
            if (checkEqual(toFind, formula)) {
                if (checkIsNotFree(v->l, v->r->l->s)) {
                    return true;
                } else {
                    throw VariableFreeError(v->l, v->r->l->s);
                }
            }
        }
    }
    return false;
}

bool checkExistsRule(Node *v, const vector<Node*> &formulas) {
    if (v->s == "->" && v->l->s == "?") {
        Node *toFind = new Node("->", v->l->r, v->r);
        /*if (checkIsNotFree(v->r, v->l->l->s)) {
            for (Node *formula : formulas) {
                if (checkEqual(toFind, formula)) {
                    return true;
                }
            }
        } else {
            throw VariableFreeError(v->r, v->l->l->s);
        }*/
        for (int i = 0; i < formulas.size(); i++) {
            Node *formula = formulas[i];
            if (checkEqual(toFind, formula)) {
                //if (count==228)cout << formula->getAsString() << "\n" << toFind->getAsString() << "\n" << i + 2 << "\n";
                if (checkIsNotFree(v->r, v->l->l->s)) {
                    return true;
                } else {
                    throw VariableFreeError(v->r, v->l->l->s);
                }
            }
        }
    }
    return false;
}

bool parseTitle(const string &ss, vector<Node*> &supposes, Node *&alpha, Node *&betta) {
    const string s = getStringWithoutSpaces(ss);
    for (int i = 0; i < s.length() - 1; i++) {
        if (s[i] == '|' && s[i+1] == '-') {
            int ptr = i + 2;
            betta = parseExpression(s, ptr);
            if (i == 0) return true;
            const string t = s.substr(0, i);
            ptr = 0;
            while (ptr < t.length()) {
                Node *expr = parseExpression(t, ptr);
                if (ptr < t.length() && t[ptr] != ',') throw "bad supposes list";
                if (ptr < t.length()) {
                    supposes.push_back(expr);
                } else {
                    alpha = expr;
                }
                ptr++;
            }

            return true;
        }
    }
    return false;
}

bool checkIsSuppose(Node *formula, const vector<Node*> &supposes) {
    for (Node *suppose : supposes) {
        if (checkEqual(suppose, formula)) {
            return true;
        }
    }
    return false;
}

Node *checkIsModusPonens(Node *formula, const vector<Node*> &formulas) {
    for (Node *vf : formulas) {
        if (vf->s == "->" && checkEqual(vf->r, formula)) {
            for (Node *v : formulas) {
                if (checkEqual(v, vf->l)) {
                    return v;
                }
            }
        }
    }
    return NULL;
}

bool checkVarIsFreeInFormula(const string &a, Node *v, bool isFree = true) {
    if (!v) {
        return false;
    }
    if (v->isVariable()) {
        if (v->s == a) {
            return isFree;
        } else {
            return false;
        }
    }
    for (Node *term : v->terms) {
        if (checkVarIsFreeInFormula(a, term, isFree)) {
            return true;
        }
    }
    if (v->s == "@" || v->s == "?") {
        return checkVarIsFreeInFormula(a, v->r, (v->l->s == a ? false : true) & isFree);
    }
    if (checkVarIsFreeInFormula(a, v->l, isFree) || checkVarIsFreeInFormula(a, v->r, isFree)) {
        return true;
    }
    return false;
}

Node *getAxiom(int number, Node *a, Node *b, Node *c) {
    return getFormulaFromTemplate(axioms[number], a, b, c);
}

void getAA(Node *a, vector<Node*> &proof) {
    proof.push_back(getAxiom(1, a, a));
    proof.push_back(getAxiom(1, a, new Node("->", a, a)));
    proof.push_back(getAxiom(2, a, new Node("->", a, a), a));
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
}

void simpleDeduction(
        const vector<Node*> &formulas,
        const vector<Node*> &supposes,
        Node *alpha,
        Node *betta,
        vector<Node*> &proof,
        int supBegin_ = 0, int supEnd_ = -1,
        int forBegin_ = 0, int forEnd_ = -1) {
    if (supEnd_ == -1) {
        supEnd_ = supposes.size();
    }
    if (forEnd_ == -1) {
        forEnd_ = formulas.size();
    }

    if (!checkEqual(formulas[forEnd_ - 1], betta)) {
        throw "Deduction fail : last formula != betta";
    }

    for (int i = forBegin_; i < forEnd_; i++) {
        Node * expr = formulas[i];
        int axiomNumber = checkIsAxiom(expr);
        int proofStart = proof.size();
        if (axiomNumber != -1 || checkIsSuppose(expr, supposes)) {
            // di
            proof.push_back(expr);
            // di -> (a -> di)
            proof.push_back(getAxiom(1, expr, alpha));
            proof.push_back(proof.back()->r);
        } else if (checkEqual(expr, alpha)) {
            getAA(alpha, proof);
        } else {
            Node *dj = checkIsModusPonens(expr, formulas);
            if (dj != NULL) {
                //Node * dk = formulas[mp.second];
                // (a -> dj) -> ((a -> (dj -> di))) -> (a -> di)
                proof.push_back(getAxiom(2, alpha, dj, expr));
                // ((a -> (dj -> di))) -> (a -> di)
                proof.push_back(proof.back()->r);
                // a -> di
                proof.push_back(proof.back()->r);
            } else {
                cout << "OOPS: " << "\n" << expr->getAsString() << "\n";
                throw "there is an error in proof";
            }
        }
    }
}

void simpleDeductionFormal(
        const vector<Node *> &formulas,
        const vector<Node *> &supposes,
        Node *alpha, Node *betta,
        vector<Node *> &proof) {
    int counter = 0;
    try {
        for (Node *formula : formulas) {
            counter++;
            int axiomNumber = -1;

            axiomNumber = checkIsAxiom(formula);
            int type = 0;
            if (axiomNumber != -1) {
                type = 1;
                //                cout << "axiom " << axiomNumber << "\n";
                if (axiomNumber == 21) {
                    if (checkVarIsFreeInFormula(formula->l->r->l->s, alpha)) {
                        throw KvantorError("аксиома", formula->l->r->l->s, alpha);
                    }
                }
                /*
                if (axiomNumber == 11) {
                    if (checkVarIsFreeInFormula(formula->l->l->s, alpha)) {
                        throw KvantorError("аксиома", formula->l->l->s, alpha);
                    }
                }
                if (axiomNumber == 12) {
                    if (checkVarIsFreeInFormula(formula->r->l->s, alpha)) {
                        throw KvantorError("аксиома", formula->r->l->s, alpha);
                    }
                }
                */
                proof.push_back(formula);
                proof.push_back(getAxiom(1, formula, alpha));
                proof.push_back(proof.back()->r);

            } else if (checkIsSuppose(formula, supposes)) {
                type = 2;
                //                cout << "suppose" << "\n";
                proof.push_back(formula);
                proof.push_back(getAxiom(1, formula, alpha));
                proof.push_back(proof.back()->r);
            } else if (checkEqual(formula, alpha)) {
                type = 3;
                //                cout << "alpha " << "\n";
                getAA(alpha, proof);
            } else if (checkForallRule(formula, formulas)) {
                type = 4;
                //                cout << "forall rule" << "\n";
                if (checkVarIsFreeInFormula(formula->r->l->s, alpha)) {
                    throw KvantorError("правило", formula->r->l->s, alpha);
                }
                if (checkVarIsFreeInFormula(formula->r->l->s, formula->l)) {
                    throw VariableFreeError(formula->l, formula->r->l->s);
                }
                //for (Node *v : supposes) {
                //    if (checkVarIsFreeInFormula(formula->r->l->s, v)) {
                //        throw VariableFreeError(v, formula->r->l->s);
                //    }
                //}

                vector<Node*> tmpSupposes;
                vector<Node*> tmpFormulas;
                vector<Node*> tmpProof;

                Node *A = alpha;
                Node *B = formula->l;
                Node *C = formula->r->r;
                ////////////////////////////////////////////////////
                /// A->(B->C), A&B |- C ...
                tmpSupposes.push_back(new Node("->", A, new Node("->", B, C)));

                tmpFormulas.push_back(new Node("&", A, B));
                tmpFormulas.push_back(getAxiom(4, A, B));
                tmpFormulas.push_back(A);
                tmpFormulas.push_back(getAxiom(5, A, B));
                tmpFormulas.push_back(B);
                tmpFormulas.push_back(tmpSupposes[0]);
                tmpFormulas.push_back(tmpFormulas.back()->r);
                tmpFormulas.push_back(tmpFormulas.back()->r);

                simpleDeduction(tmpFormulas, tmpSupposes, tmpFormulas[0], C, proof);
                /// ... A&B -> C
                ////////////////////////////////////////////////////
                /// A&B -> @xC
                proof.push_back(new Node("->", tmpFormulas[0], formula->r));
                ////////////////////////////////////////////////////
                /// A&B->@xC,A,B |- @xC ...
                tmpSupposes.clear();
                tmpFormulas.clear();
                tmpSupposes.push_back(proof.back());
                tmpSupposes.push_back(A);

                tmpFormulas.push_back(A);
                tmpFormulas.push_back(B);
                tmpFormulas.push_back(getAxiom(3, A, B));
                tmpFormulas.push_back(tmpFormulas.back()->r);
                tmpFormulas.push_back(tmpFormulas.back()->r);
                tmpFormulas.push_back(tmpSupposes[0]);
                tmpFormulas.push_back(tmpFormulas.back()->r);

                simpleDeduction(tmpFormulas, tmpSupposes, B, formula->r, tmpProof);
                /// ... A&B->@xC,A |- B->@xC ...
                tmpSupposes.pop_back();

                simpleDeduction(tmpProof, tmpSupposes, A, tmpProof.back(), proof);
                /// ... A->B->@xC
                ////////////////////////////////////////////////////

            } else if (checkExistsRule(formula, formulas)) {
                type = 5;
                //                cout << "exists rule" << "\n";

                if (checkVarIsFreeInFormula(formula->l->l->s, alpha)) {
                    throw KvantorError("правило", formula->l->l->s, alpha);
                }

                if (checkVarIsFreeInFormula(formula->l->l->s, formula->r)) {
                    throw VariableFreeError(formula->r, formula->l->l->s);
                }
                //                        for (Node *v : supposes) {
                //                            if (checkVarIsFreeInFormula(formula->l->l->s, v)) {
                //                                throw VariableFreeError(v, formula->l->l->s);
                //                            }
                //                        }

                Node *A = alpha;
                Node *B = formula->l->r;
                Node *C = formula->r;
                vector<Node*> tmpSupposes;
                vector<Node*> tmpFormulas;
                vector<Node*> tmpProof;

                /// A->B->C |- B->A->C
                /// A->B->C, B, A |- C ...
                tmpSupposes.push_back(new Node("->", A, new Node("->", B, C)));
                tmpSupposes.push_back(B);

                tmpFormulas.push_back(A);
                tmpFormulas.push_back(B);
                tmpFormulas.push_back(tmpSupposes[0]);
                tmpFormulas.push_back(tmpFormulas.back()->r);
                tmpFormulas.push_back(tmpFormulas.back()->r);

                simpleDeduction(tmpFormulas, tmpSupposes, A, C, tmpProof);
                /// ... A->B->C, B |- A->C
                tmpSupposes.pop_back();

                simpleDeduction(tmpProof, tmpSupposes, B, new Node("->", A, C), proof);
                /// ... A->B->C |- B->(A->C)

                /// ?xB->(A->C)
                proof.push_back(new Node("->", formula->l, new Node("->", A, C)));
                ////////////////////////////////////////////////////
                /// ?xB->(A->C) |- A->(?xB->C)
                /// ?xB->(A->C), A, ?xB |- C ...
                tmpSupposes.clear();
                tmpFormulas.clear();
                tmpSupposes.push_back(proof.back());
                tmpSupposes.push_back(A);

                tmpFormulas.push_back(A);
                tmpFormulas.push_back(tmpSupposes[0]->l);
                tmpFormulas.push_back(tmpSupposes[0]);
                tmpFormulas.push_back(tmpFormulas.back()->r);
                tmpFormulas.push_back(tmpFormulas.back()->r);

                simpleDeduction(tmpFormulas, tmpSupposes, tmpSupposes[0]->l, C, tmpProof);
                /// ... ?xB->(A->C), A |- ?xB->C
                tmpSupposes.pop_back();
                simpleDeduction(tmpProof, tmpSupposes, A, formula, proof);
                /// ... A->(?xB->C)
                ////////////////////////////////////////////////////

            } else {
                type = 6;
                Node *v = checkIsModusPonens(formula, formulas);
                if (v != NULL) {
                    //                    cout << "modus ponens" << "\n";
                    proof.push_back(getAxiom(2, alpha, v, formula));
                    proof.push_back(proof.back()->r);
                    proof.push_back(proof.back()->r);
                } else {
                    //                    cout << "uknown stuff" << "\n";
                    throw UnknownError();
                }
            }
        }
    } catch (const SubstituteError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "терм " << e.x->getAsString()
        << " не свободен для подстановки в формулу " << e.y->getAsString()
        << " вместо переменной " << e.a << ".\n";
    } catch (const VariableFreeError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "переменная " << e.a << " входит свободно в формулу " << e.x->getAsString() << ".\n";
    } catch (const KvantorError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "используется " << e.type << " с квантором по переменной " << e.a
        << ", входящей свободно в допущение " << e.x->getAsString() << ".\n";
    } catch (const UnknownError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ".\n";
    } catch (const char *c) {
        cout << c << "\n";
    }

    /*} catch (const SubstituteError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "терм " << e.x->getAsString()
             << " не свободен для подстановки в формулу " << e.y->getAsString()
             << " вместо переменной " << e.a << ".\n";
    } catch (const VariableFreeError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "переменная " << e.a << " входит свободно в формулу " << e.x->getAsString() << ".\n";
    } catch (const KvantorError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "используется " << e.type << " с квантором по переменной " << e.a
             << ", входящей свободно в допущение " << e.x->getAsString() << ".\n";
    } catch (const UnknownError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ".\n";
    } catch (const char *c) {
        cout << c << "\n";
    }*/

}

Node *setAllKvantor(Node *v, string s) {
    return new Node("->", v->l, new Node("@", new Node(s, NULL, NULL), v->r));
}

Node *renameVars(vector<Node *> &proof, Node *a, string oldA, Node *newA
        , string oldB, Node *newB , string oldC, Node *newC) {

    proof.push_back(CONST);
    proof.push_back(a);
    proof.push_back(getAxiom(1, a, CONST));
    proof.push_back(proof.back()->r);
    proof.push_back(setAllKvantor(proof.back(), oldC));
    proof.push_back(setAllKvantor(proof.back(), oldB));
    proof.push_back(setAllKvantor(proof.back(), oldA));
    proof.push_back(proof.back()->r);

    bool tmp = true;
    Node *sub = substitute(proof.back()->r, oldA, newA, tmp);
    proof.push_back(new Node("->", proof.back(), sub));
    proof.push_back(proof.back()->r);

    tmp = true;
    sub = substitute(proof.back()->r, oldB, newB, tmp);
    proof.push_back(new Node("->", proof.back(), sub));
    proof.push_back(proof.back()->r);

    tmp = true;
    sub = substitute(proof.back()->r, oldC, newC, tmp);
    proof.push_back(new Node("->", proof.back(), sub));
    proof.push_back(proof.back()->r);

    return proof.back();
}

#endif // NODEPARSER_H
#ifndef NODEPARSER_H
#define NODEPARSER_H

#include <map>
#include <string>
#include <vector>

using namespace std;

const int N = 5000;

int count = 0;
long long prime[N * N];

string getStringWithoutSpaces(const string & s) {
    string res = "";
    for (unsigned int i = 0; i < s.length(); i++) {
        char c = s[i];
        if (!isspace(c)) res += c;
    }
    return res;
}

struct Node {
    bool hasKvantors;
    bool isPredvar;
    long long hash;
    int vertCnt;
    int ptrCnt;
    bool lastValue;
    vector<Node*> terms;
    string s;
    Node * l;
    Node * r;
    Node() : vertCnt(0), ptrCnt(0), l(NULL), r(NULL) {}
    Node(string s, Node * l, Node * r) : s(s), l(l), r(r) {
        if (s == "?" || s == "@") {
            hasKvantors = true;
            isPredvar = r->isPredvar;
        } else {
            hasKvantors = (l ? l->hasKvantors : false) | (r ? r->hasKvantors : false);
            isPredvar = !(l ? l->hasKvantors : false) & !(r ? r->hasKvantors : false);
        }
        //if (isPredvar) cout << getAsString() << "\n";
        //cout << s << "\n";
        vertCnt = 1;
        ptrCnt = 0;
        int lCnt = 0, rCnt = 0;
        if (l) {
            lCnt  = l->vertCnt;
            vertCnt += lCnt;
            l->ptrCnt++;
        }
        if (r) {
            rCnt  = r->vertCnt;
            vertCnt += rCnt;
        }
        hash = 0;
        if (l) hash += l->hash;
        for (int i = 0; i < s.length(); i++) {
            hash *= prime[1];
            hash += s[i];
        }
        if (r) {
            hash *= prime[rCnt];
            hash += r->hash;
            r->ptrCnt++;
        }

    }
    Node(string s, vector<Node*> &terms) : Node(s, NULL, NULL) {
        this->terms = terms;
        hash = terms[0]->hash;
        for (int i = 1; i < terms.size(); i++) {
            hash *= prime[terms[i]->vertCnt];
            hash += terms[i]->hash;
        }
        for (int i = 0; i < s.length(); i++) {
            hash *= prime[1];
            hash += s[i];
        }
    }

    ~Node() {
        if (l && l->ptrCnt == 0) delete l;
        if (r && r->ptrCnt == 0) delete r;
    }

    string getAsString(bool isMain = true) {
        string result = "";
        bool isInc = false;
        if (s[0] == '\'' && (l->s[0] == '\'' || !l->l && !l->r)) {
            isInc = true;
        }
        if (!isVariable() && !isMain && !isInc && !isNil()) {
            result += "(";
        }
        if (s != "@" && s != "?") {
            if (l) {
                result += l->getAsString(false);
            }
            result += s;
        } else {
            result += s;
            if (l) {
                result += l->getAsString(false);
            }
        }
        if (r) {
            result += r->getAsString(false);
        }
        if (terms.size() != 0) {
            result += "(";
            for (int i = 0; i < terms.size() - 1; i++) {
                result += terms[i]->getAsString() + ",";
            }
            result += terms.back()->getAsString();
            result += ")";
        }
        if (!isVariable() && !isMain && !isInc && !isNil()) {
            result += ")";
        }
        return result;
    }

    bool isNil() {
        return s.length() == 1 && s[0] == '0';
    }

    bool isVariable() {
        if (s.length() > 0 && s[0] >= 'a' && s[0] <= 'z' && terms.size() == 0) {
            return true;
        }
        return false;
    }

    bool isFunction() {
        if (s.length() > 0 &&
             (
                (s[0] >= 'a' && s[0] <= 'z' && terms.size() != 0) ||
                    s[0] == '\'' || s[0] == '*' || s[0] == '+' || s[0] == '0'
             )) {
            return true;
        }
        return false;
    }

    bool isPredicate() {
        if (s.length() > 0 && s[0] >= 'A' && s[0] <= 'Z') {
            return true;
        }
        return false;
    }
};

Node *NIL;
Node *A;
Node *CONST;

struct SubstituteError {
    Node *x, *y;
    string a;
    // y[a:=x]
    SubstituteError(Node *y, const string &a, Node *x) : x(x), y(y), a(a) {}
};

struct VariableFreeError {
    Node *x;
    string a;
    VariableFreeError(Node *x, const string &a) : x(x), a(a) {}
};

struct KvantorError {
    string type;
    string a;
    Node *x;
    KvantorError(const string &type, const string &a, Node *x) : type(type), a(a), x(x) {}
};

struct UnknownError {

};

Node *notX(Node *x) {
    return new Node("!", NULL, x);
}

Node *notNotX(Node *x) {
    return notX(notX(x));
}

vector<Node*> axioms;

bool checkEqual(Node * a, Node * b) {
    if (!a && !b) return true;
    if (!a || !b) return false;
    if (a == b) return true;
    if (a->hash != b->hash) return false;
    else return true;
    if (a->terms.size() != b->terms.size()) return false;
    if (a->s != b->s) return false;
    for (int i = 0; i < a->terms.size(); i++) {
        if (!checkEqual(a->terms[i], b->terms[i])) {
            return false;
        }
    }
    if (!checkEqual(a->l, b->l)) return false;
    if (!checkEqual(a->r, b->r)) return false;
    return true;
}




Node *parseExpression(const string &s, int &ptr);
Node *parseDisjuction(const string &s, int &ptr);
Node *parseConjuction(const string &s, int &ptr);
Node *parseUnary(const string &s, int &ptr);
Node *parsePredicate(const string &s, int &ptr);
Node *parseTerm(const string &s, int &ptr);
Node *parseSummand(const string &s, int &ptr);
Node *parseMultiplied(const string &s, int &ptr);
Node *parseLowLevelMultiplied(const string &s, int &ptr);
void getAA(Node *a, vector<Node*> &proof);

Node * parseLowLevelMultiplied(const string &s, int &ptr) {
    if (ptr >= s.length()) return NULL;
    char c = s[ptr];
    if (c >= 'a' && c <= 'z') {
        string name;
        name += c;
        ptr++;
        while (ptr < s.length() && s[ptr] >= '0' && s[ptr] <= '9') {
            name += s[ptr++];
        }
        if (ptr < s.length() && s[ptr] == '(')  {
            ptr++;
            vector<Node*> terms;
            terms.push_back(parseTerm(s, ptr));
            while (ptr < s.length() && s[ptr] == ',') {
                ptr++;
                terms.push_back(parseTerm(s, ptr));
            }
            if (ptr == s.length() || s[ptr++] != ')') throw ") after function end expected";
            return new Node(name, terms);
        } else {
            return new Node(name, NULL, NULL);
        }
    } else if (c == '(') {
        ptr++;
        Node *res = parseTerm(s, ptr);
        if (ptr == s.length() || s[ptr++] != ')') throw ") in parseMultiplied expected";
        return res;
    } else if (c == '0') {
        ptr++;
        return new Node("0", NULL, NULL);
    }
    throw "Incorrect multiplied";
}

Node * parseMultiplied(const string &s, int &ptr) {
    Node *res = parseLowLevelMultiplied(s, ptr);
    while (ptr < s.length() && s[ptr] == '\'') {
        res = new Node("'", res, NULL);
        ptr++;
    }
    return res;
}

Node * parseSummand(const string &s, int &ptr) {
    Node * expr = parseMultiplied(s, ptr);
    while (ptr < s.length() && s[ptr] == '*') {
        ptr++;
        Node * expr2 = parseMultiplied(s, ptr);
        expr = new Node("*", expr, expr2);
    }
    return expr;
}

Node * parseTerm(const string &s, int &ptr) {
    Node * expr = parseSummand(s, ptr);
    while (ptr < s.length() && s[ptr] == '+') {
        ptr++;
        Node * expr2 = parseSummand(s, ptr);
        expr = new Node("+", expr, expr2);
    }
    return expr;
}

Node * parsePredicate(const string &s, int &ptr) {
    if (ptr >= s.length()) return NULL;
    char c = s[ptr];
    if (c >= 'A' && c <= 'Z') {
        string name;
        name += c;
        ptr++;
        while (ptr < s.length() && s[ptr] >= '0' && s[ptr] <= '9') {
            name += s[ptr++];
        }

        if (ptr == s.length() || s[ptr] != '(') {
            return new Node(name, NULL, NULL);
        }
        ptr++;
        vector<Node*> terms;
        terms.push_back(parseTerm(s, ptr));
        while (ptr < s.length() && s[ptr] == ',') {
            ptr++;
            terms.push_back(parseTerm(s, ptr));
        }
        if (ptr == s.length() || s[ptr++] != ')') throw ") after predicate end expected";
        return new Node(name, terms);
    } else {
        Node *term1 = parseTerm(s, ptr);
        if (s[ptr++] != '=') throw "= in predicate expected";
        Node *term2 = parseTerm(s, ptr);
        return new Node("=", term1, term2);
    }
}

Node * parseUnary(const string &s, int &ptr) {
    if (ptr >= s.length()) return NULL;
    const char c = s[ptr];
    const int fPtr = ptr;

    Node *v1 = NULL;
    try {
        if (c == '@' || c == '?') {
            ptr++;
            if (s[ptr] < 'a' || s[ptr] > 'z') {
                throw string("a...z after ") + c + string(" expected");
            }
            string name;
            name += s[ptr++]; // >= 'a' and <= 'z'
            while (ptr < s.length() && s[ptr] >= '0' && s[ptr] <= '9') {
                name += s[ptr++];
            }
            v1 = new Node(c == '?' ? "?" : "@", new Node(name, NULL, NULL), parseUnary(s, ptr));
        }
    } catch(...) {
        v1 = NULL;
    }
    if (v1) {
        return v1;
    }

    ptr = fPtr;
    try {
        if (c == '!') {
            ptr++;
            Node *expr = parseUnary(s, ptr);
            v1 = notX(expr);
        }
    } catch(...) {
        v1 = NULL;
    }
    if (v1) {
        return v1;
    }

    ptr = fPtr;
    try {
        if (c == '(') {
            ptr++;
            Node * expr = parseExpression(s, ptr);
            if (ptr >= s.length() || s[ptr++] != ')') {
                throw ") doesn't exist";
            }
            return expr;
        }
    } catch(...) {
        v1 = NULL;
    }
    if (v1) {
        return v1;
    }

    ptr = fPtr;
    return parsePredicate(s, ptr);

}

Node * parseConjuction(const string &s, int &ptr) {
    Node * expr = parseUnary(s, ptr);
    while (ptr < s.length() && s[ptr] == '&') {
        ptr++;
        Node * expr2 = parseUnary(s, ptr);
        expr = new Node("&", expr, expr2);
    }
    return expr;
}

Node * parseDisjuction(const string &s, int &ptr) {
    Node * expr = parseConjuction(s, ptr);
    while (ptr < s.length() && s[ptr] == '|') {
        ptr++;
        Node * expr2 = parseConjuction(s, ptr);
        expr = new Node("|", expr, expr2);
    }
    return expr;
}

Node * parseExpression(const string &s, int &ptr) {
    Node * expr1 = parseDisjuction(s, ptr);
    if (ptr < s.length() && s[ptr] == '-' && s[++ptr] == '>') {
        ptr++;
        Node * expr2 = parseExpression(s, ptr);
        return new Node("->", expr1, expr2);
    }
    return expr1;
}

Node * parseStringToFormula(const string &s) {
    int ptr = 0;
    string ss = getStringWithoutSpaces(s);
    return parseExpression(ss, ptr);
}


// by predicate or by variable
bool fillMap(Node * formula, Node * template_, map<string, vector<Node *> > &variableMap, bool byPred = true) {
    if (!formula && !template_) return true;
    if (!formula || !template_) return false;
    const string &tempStr = template_->s;
    if (byPred && template_->isPredicate() || !byPred && template_->isVariable()) {
        variableMap[tempStr].push_back(formula);
        return true;
    } else {
        if (tempStr != formula->s) {
            return false;
        }
        return fillMap(formula->l, template_->l, variableMap, byPred) &&
                fillMap(formula->r, template_->r, variableMap, byPred);
    }
}

// by predicate or by variable
bool checkFormulaIsSimilarToTemplate(Node *formula, Node *template_, bool byPred = true) {
    if (!formula && !template_) return true;
    if (!formula || !template_) return false;
    if (formula == template_) return true;
    map<string, vector<Node*> > variableMap;
    if (fillMap(formula, template_, variableMap, byPred)) {
        for (auto& it : variableMap) {
            vector<Node*> &nodes = it.second;
            for (Node* node : nodes) {
                if (!checkEqual(node, *nodes.begin())) {
                    return false;
                }
            }
        }
        return true;
    }
    return false;
}

// for 11, 12, 21 axioms
bool checkFormulaIsSimilarToTemplate2(Node *formula, Node *template_) {
    if (!formula && !template_) return true;
    if (!formula || !template_) return false;
    if (formula == template_) return true;
    if (template_->isVariable()) {
        return formula->isVariable();
    }
    if (template_->isPredicate()) {
        return true;
    }
    if (formula->s != template_->s) {
        return false;
    }
    return checkFormulaIsSimilarToTemplate2(formula->l, template_->l) &&
            checkFormulaIsSimilarToTemplate2(formula->r, template_->r);
}

Node *getFirstNotBound(Node *formula, Node *template_, const string &x) {
    if (!formula || !template_) return NULL;
    if (template_->s == x) {
        return formula;
    }

    if (template_->s != formula->s) {
        return NULL;
    }

    if (template_->terms.size() != formula->terms.size()) {
        return NULL;
    }

    bool isKvant = false;
    if (formula->s == "@" || formula->s == "?") {
        if (formula->l->s == x) {
            return NULL;
        }
        isKvant = true;
    }

    for (int i = 0; i < formula->terms.size(); i++) {
        Node *res = getFirstNotBound(formula->terms[i],
                                     template_->terms[i],
                                     x);
        if (res) return res;
    }

    if (!isKvant) {
        Node *res1 = getFirstNotBound(formula->l, template_->l, x);
        if (res1) return res1;
    }
    Node *res2 = getFirstNotBound(formula->r, template_->r, x);
    if (res2) return res2;
}

bool checkIsFreeForSub(Node *v, const map<string, int> &bounded) {
    if (!v) return true;
    for (Node *term : v->terms) {
        if  (!checkIsFreeForSub(term, bounded)) {
            return false;
        }
    }
    if (v->isVariable()) {
        auto it = bounded.find(v->s);
        return it == bounded.end() || it->second == 0;
    }
    return checkIsFreeForSub(v->l, bounded) && checkIsFreeForSub(v->r, bounded);
}

bool checkIsNotFree(Node *v, const string &x, map<string, int> &bounded) {
    if (!v) return true;
    if (v->s == "@" || v->s == "?") {
        bounded[v->l->s]++;
    }

    if (v->isVariable()) {
        auto it = bounded.find(v->s);
        return it == bounded.end() || it->second != 0;
    }
    bool result = checkIsNotFree(v->l, x, bounded) && checkIsNotFree(v->r, x, bounded);
    if (v->s == "@" || v->s == "?") {
        bounded[v->l->s]--;
    }
    return result;
}

bool checkIsNotFree(Node *v, const string &x) {
    map<string, int> bounded;
    return checkIsNotFree(v, x, bounded);
}

Node *substitute(Node *alpha, const string &x, Node *tetta, map<string, int> &bounded, bool &isFree) {
    if (!alpha) return NULL;

    bool isKvant = false;
    if (alpha->s == "@" || alpha->s == "?") {
        if (alpha->l->s == x) {
            return alpha;
        }
        bounded[alpha->l->s]++;
        isKvant = true;
        return new Node(alpha->s,
                        alpha->l,
                        substitute(alpha->r, x, tetta, bounded, isFree));
    }
    Node *result = NULL;
    if (alpha->s == x) {
        if (!checkIsFreeForSub(tetta, bounded)) {
            isFree = false;
        }
        result = tetta;
    } else {
        if (alpha->terms.size() == 0) {
            result = new Node(alpha->s,
                            substitute(alpha->l, x, tetta, bounded, isFree),
                            substitute(alpha->r, x, tetta, bounded, isFree));
        } else {
            vector<Node*> terms;
            for (Node *term : alpha->terms) {
                terms.push_back(substitute(term, x, tetta, bounded, isFree));
            }
            result = new Node(alpha->s, terms);
        }
    }
    if (isKvant) {
        bounded[alpha->l->s]--;
    }
    return result;
}

// alpha[x:=tetta]
Node *substitute(Node *alpha, const string &x, Node *tetta, bool &isFree) {
    map<string, int> bounded;
    Node *result = substitute(alpha, x, tetta, bounded, isFree);
    return result;
}

Node *substitute(Node *alpha, const string &x, Node *tetta) {
    bool isFree = true;
    return substitute(alpha, x, tetta, isFree);
}

Node *getFormulaFromTemplate(Node *v, Node *a = NULL, Node *b = NULL, Node *c = NULL) {
    if (!v) return NULL;
    if (v->s == "A") return a;
    if (v->s == "B") return b;
    if (v->s == "C") return c;
    return new Node(v->s,
                    getFormulaFromTemplate(v->l, a, b, c),
                    getFormulaFromTemplate(v->r, a, b, c));
}

Node *getAxiom(int, Node *a = NULL, Node *b = NULL, Node *c = NULL);

void init() {
    prime[0] = 1;
    prime[1] = 31;
    for (int i = 2; i < N * N; i++) {
        prime[i] = prime[i - 1] * prime[1];
    }
    axioms = vector<Node*>(30);
    axioms[1] = parseStringToFormula("A->B->A");
    axioms[2] = parseStringToFormula("(A->B)->(A->B->C)->(A->C)");
    axioms[3] = parseStringToFormula("A->B->A&B");
    axioms[4] = parseStringToFormula("A&B->A");
    axioms[5] = parseStringToFormula("A&B->B");
    axioms[6] = parseStringToFormula("A->A|B");
    axioms[7] = parseStringToFormula("B->A|B");
    axioms[8] = parseStringToFormula("(A->C)->(B->C)->(A|B->C)");
    axioms[9] = parseStringToFormula("(A->B)->(A->!B)->!A");
    axioms[10] = parseStringToFormula("!!A->A");

    axioms[11] = parseStringToFormula("@xA->A(x)");
    axioms[12] = parseStringToFormula("A(x)->?xA");

    axioms[13] = parseStringToFormula("a=b->a'=b'");
    axioms[14] = parseStringToFormula("a=b->a=c->b=c");
    axioms[15] = parseStringToFormula("a'=b'->a=b");
    axioms[16] = parseStringToFormula("!a'=0");
    axioms[17] = parseStringToFormula("a+b'=(a+b)'");
    axioms[18] = parseStringToFormula("a+0=a");
    axioms[19] = parseStringToFormula("a*0=0");
    axioms[20] = parseStringToFormula("a*b'=a*b+a");
    axioms[21] = parseStringToFormula("A(x)&@x(A->A(x))->A");

    NIL = new Node("0", NULL, NULL);
    A = new Node("a", NULL, NULL);
    Node *tmp = new Node("=", NIL, NIL);
    CONST = getAxiom(1, tmp, tmp);
}

int checkIsAxiom(Node *formula) {
    for (int i = 1; i <= 10; i++) {
        if (checkFormulaIsSimilarToTemplate(formula, axioms[i])) {
            return i;
        }
    }
    if (checkFormulaIsSimilarToTemplate2(formula, axioms[11])) {
        Node *x = getFirstNotBound(formula->r,
                                   formula->l->r,
                                   formula->l->l->s);
                                   //cout << x << "\n";
        if (x) {
            bool isFree = true;
            Node *sub = substitute(formula->l->r,
                                   formula->l->l->s,
                                   x, isFree);
            if (checkEqual(sub, formula->r)) {
                if (isFree) {
                    return 11;
                } else {
                    throw SubstituteError(formula->l->r,
                                          formula->l->l->s,
                                          x);
                }
            }
        } else {
            if (checkEqual(formula->l->r, formula->r)) return 11;
        }
    }
    if (checkFormulaIsSimilarToTemplate2(formula, axioms[12])) {
        Node *x = getFirstNotBound(formula->l,
                                   formula->r->r,
                                   formula->r->l->s);
        if (x) {
            bool isFree = true;
            Node *sub = substitute(formula->r->r,
                                   formula->r->l->s,
                                   x, isFree);
            if (checkEqual(sub, formula->l)) {
                if (isFree) {
                    return 12;
                } else {
                    throw SubstituteError(formula->r->r,
                                          formula->r->l->s,
                                          x);
                }
            }
        } else {
            if (checkEqual(formula->r->r, formula->l)) return 12;
        }
    }

    for (int i = 13; i <= 20; i++) {
        //if (checkFormulaIsSimilarToTemplate(formula, axioms[i], false)) {
        if (checkEqual(formula, axioms[i])) {
            return i;
        }
    }
    if (checkFormulaIsSimilarToTemplate2(formula, axioms[21])) {
        if (checkEqual(formula->r, formula->l->r->r->l)) {
            const string &x = formula->l->r->l->s;
            bool isFree = true;
            Node *sub0 = substitute(formula->r, x, new Node("0", NULL, NULL), isFree);
            if (checkEqual(sub0, formula->l->l)) {
                Node *subx = substitute(formula->r, x, new Node("\'", new Node(x, NULL, NULL), NULL), isFree);
                if (checkEqual(subx, formula->l->r->r->r)) {
                    return 21;
                }
            }
        }
    }

    return -1;
}

bool checkForallRule(Node *v, const vector<Node*> &formulas) {
    if (v->s == "->" && v->r->s == "@") {
        Node *toFind = new Node("->", v->l, v->r->r);
       /* if (checkIsNotFree(v->l, v->r->l->s)) {
            for (Node *formula : formulas) {
                if (checkEqual(toFind, formula)) {
                    return true;
                }
            }
        } else {
            throw VariableFreeError(v->l, v->r->l->s);
        }*/
        for (Node *formula : formulas) {
            if (checkEqual(toFind, formula)) {
                if (checkIsNotFree(v->l, v->r->l->s)) {
                    return true;
                } else {
                    throw VariableFreeError(v->l, v->r->l->s);
                }
            }
        }
    }
    return false;
}

bool checkExistsRule(Node *v, const vector<Node*> &formulas) {
    if (v->s == "->" && v->l->s == "?") {
        Node *toFind = new Node("->", v->l->r, v->r);
        /*if (checkIsNotFree(v->r, v->l->l->s)) {
            for (Node *formula : formulas) {
                if (checkEqual(toFind, formula)) {
                    return true;
                }
            }
        } else {
            throw VariableFreeError(v->r, v->l->l->s);
        }*/
        for (int i = 0; i < formulas.size(); i++) {
            Node *formula = formulas[i];
            if (checkEqual(toFind, formula)) {
                //if (count==228)cout << formula->getAsString() << "\n" << toFind->getAsString() << "\n" << i + 2 << "\n";
                if (checkIsNotFree(v->r, v->l->l->s)) {
                    return true;
                } else {
                    throw VariableFreeError(v->r, v->l->l->s);
                }
            }
        }
    }
    return false;
}

bool parseTitle(const string &ss, vector<Node*> &supposes, Node *&alpha, Node *&betta) {
    const string s = getStringWithoutSpaces(ss);
    for (int i = 0; i < s.length() - 1; i++) {
        if (s[i] == '|' && s[i+1] == '-') {
            int ptr = i + 2;
            betta = parseExpression(s, ptr);
            if (i == 0) return true;
            const string t = s.substr(0, i);
            ptr = 0;
            while (ptr < t.length()) {
                Node *expr = parseExpression(t, ptr);
                if (ptr < t.length() && t[ptr] != ',') throw "bad supposes list";
                if (ptr < t.length()) {
                    supposes.push_back(expr);
                } else {
                    alpha = expr;
                }
                ptr++;
            }

            return true;
        }
    }
    return false;
}

bool checkIsSuppose(Node *formula, const vector<Node*> &supposes) {
    for (Node *suppose : supposes) {
        if (checkEqual(suppose, formula)) {
            return true;
        }
    }
    return false;
}

Node *checkIsModusPonens(Node *formula, const vector<Node*> &formulas) {
    for (Node *vf : formulas) {
        if (vf->s == "->" && checkEqual(vf->r, formula)) {
            for (Node *v : formulas) {
                if (checkEqual(v, vf->l)) {
                    return v;
                }
            }
        }
    }
    return NULL;
}

bool checkVarIsFreeInFormula(const string &a, Node *v, bool isFree = true) {
    if (!v) {
        return false;
    }
    if (v->isVariable()) {
        if (v->s == a) {
            return isFree;
        } else {
            return false;
        }
    }
    for (Node *term : v->terms) {
        if (checkVarIsFreeInFormula(a, term, isFree)) {
            return true;
        }
    }
    if (v->s == "@" || v->s == "?") {
        return checkVarIsFreeInFormula(a, v->r, (v->l->s == a ? false : true) & isFree);
    }
    if (checkVarIsFreeInFormula(a, v->l, isFree) || checkVarIsFreeInFormula(a, v->r, isFree)) {
        return true;
    }
    return false;
}

Node *getAxiom(int number, Node *a, Node *b, Node *c) {
    return getFormulaFromTemplate(axioms[number], a, b, c);
}

void getAA(Node *a, vector<Node*> &proof) {
    proof.push_back(getAxiom(1, a, a));
    proof.push_back(getAxiom(1, a, new Node("->", a, a)));
    proof.push_back(getAxiom(2, a, new Node("->", a, a), a));
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
}

void simpleDeduction(
        const vector<Node*> &formulas,
        const vector<Node*> &supposes,
        Node *alpha,
        Node *betta,
        vector<Node*> &proof,
        int supBegin_ = 0, int supEnd_ = -1,
        int forBegin_ = 0, int forEnd_ = -1) {
    if (supEnd_ == -1) {
        supEnd_ = supposes.size();
    }
    if (forEnd_ == -1) {
        forEnd_ = formulas.size();
    }

    if (!checkEqual(formulas[forEnd_ - 1], betta)) {
        throw "Deduction fail : last formula != betta";
    }

    for (int i = forBegin_; i < forEnd_; i++) {
        Node * expr = formulas[i];
        int axiomNumber = checkIsAxiom(expr);
        int proofStart = proof.size();
        if (axiomNumber != -1 || checkIsSuppose(expr, supposes)) {
            // di
            proof.push_back(expr);
            // di -> (a -> di)
            proof.push_back(getAxiom(1, expr, alpha));
            proof.push_back(proof.back()->r);
        } else if (checkEqual(expr, alpha)) {
            getAA(alpha, proof);
        } else {
            Node *dj = checkIsModusPonens(expr, formulas);
            if (dj != NULL) {
                //Node * dk = formulas[mp.second];
                // (a -> dj) -> ((a -> (dj -> di))) -> (a -> di)
                proof.push_back(getAxiom(2, alpha, dj, expr));
                // ((a -> (dj -> di))) -> (a -> di)
                proof.push_back(proof.back()->r);
                // a -> di
                proof.push_back(proof.back()->r);
            } else {
                cout << "OOPS: " << "\n" << expr->getAsString() << "\n";
                throw "there is an error in proof";
            }
        }
    }
}

void simpleDeductionFormal(
        const vector<Node *> &formulas,
        const vector<Node *> &supposes,
        Node *alpha, Node *betta,
        vector<Node *> &proof) {
    int counter = 0;
    try {
        for (Node *formula : formulas) {
            counter++;
            int axiomNumber = -1;

            axiomNumber = checkIsAxiom(formula);
            int type = 0;
            if (axiomNumber != -1) {
                type = 1;
    //                cout << "axiom " << axiomNumber << "\n";
                if (axiomNumber == 21) {
                    if (checkVarIsFreeInFormula(formula->l->r->l->s, alpha)) {
                        throw KvantorError("аксиома", formula->l->r->l->s, alpha);
                    }
                }
                /*
                if (axiomNumber == 11) {
                    if (checkVarIsFreeInFormula(formula->l->l->s, alpha)) {
                        throw KvantorError("аксиома", formula->l->l->s, alpha);
                    }
                }
                if (axiomNumber == 12) {
                    if (checkVarIsFreeInFormula(formula->r->l->s, alpha)) {
                        throw KvantorError("аксиома", formula->r->l->s, alpha);
                    }
                }
                */
                proof.push_back(formula);
                proof.push_back(getAxiom(1, formula, alpha));
                proof.push_back(proof.back()->r);

            } else if (checkIsSuppose(formula, supposes)) {
                type = 2;
    //                cout << "suppose" << "\n";
                proof.push_back(formula);
                proof.push_back(getAxiom(1, formula, alpha));
                proof.push_back(proof.back()->r);
            } else if (checkEqual(formula, alpha)) {
                type = 3;
    //                cout << "alpha " << "\n";
                getAA(alpha, proof);
            } else if (checkForallRule(formula, formulas)) {
                type = 4;
    //                cout << "forall rule" << "\n";
                if (checkVarIsFreeInFormula(formula->r->l->s, alpha)) {
                    throw KvantorError("правило", formula->r->l->s, alpha);
                }
                if (checkVarIsFreeInFormula(formula->r->l->s, formula->l)) {
                    throw VariableFreeError(formula->l, formula->r->l->s);
                }
                //for (Node *v : supposes) {
                //    if (checkVarIsFreeInFormula(formula->r->l->s, v)) {
                //        throw VariableFreeError(v, formula->r->l->s);
                //    }
                //}

                vector<Node*> tmpSupposes;
                vector<Node*> tmpFormulas;
                vector<Node*> tmpProof;

                Node *A = alpha;
                Node *B = formula->l;
                Node *C = formula->r->r;
                ////////////////////////////////////////////////////
                /// A->(B->C), A&B |- C ...
                tmpSupposes.push_back(new Node("->", A, new Node("->", B, C)));

                tmpFormulas.push_back(new Node("&", A, B));
                tmpFormulas.push_back(getAxiom(4, A, B));
                tmpFormulas.push_back(A);
                tmpFormulas.push_back(getAxiom(5, A, B));
                tmpFormulas.push_back(B);
                tmpFormulas.push_back(tmpSupposes[0]);
                tmpFormulas.push_back(tmpFormulas.back()->r);
                tmpFormulas.push_back(tmpFormulas.back()->r);

                simpleDeduction(tmpFormulas, tmpSupposes, tmpFormulas[0], C, proof);
                /// ... A&B -> C
                ////////////////////////////////////////////////////
                /// A&B -> @xC
                proof.push_back(new Node("->", tmpFormulas[0], formula->r));
                ////////////////////////////////////////////////////
                /// A&B->@xC,A,B |- @xC ...
                tmpSupposes.clear();
                tmpFormulas.clear();
                tmpSupposes.push_back(proof.back());
                tmpSupposes.push_back(A);

                tmpFormulas.push_back(A);
                tmpFormulas.push_back(B);
                tmpFormulas.push_back(getAxiom(3, A, B));
                tmpFormulas.push_back(tmpFormulas.back()->r);
                tmpFormulas.push_back(tmpFormulas.back()->r);
                tmpFormulas.push_back(tmpSupposes[0]);
                tmpFormulas.push_back(tmpFormulas.back()->r);

                simpleDeduction(tmpFormulas, tmpSupposes, B, formula->r, tmpProof);
                /// ... A&B->@xC,A |- B->@xC ...
                tmpSupposes.pop_back();

                simpleDeduction(tmpProof, tmpSupposes, A, tmpProof.back(), proof);
                /// ... A->B->@xC
                ////////////////////////////////////////////////////

            } else if (checkExistsRule(formula, formulas)) {
                type = 5;
        //                cout << "exists rule" << "\n";

                if (checkVarIsFreeInFormula(formula->l->l->s, alpha)) {
                    throw KvantorError("правило", formula->l->l->s, alpha);
                }

                if (checkVarIsFreeInFormula(formula->l->l->s, formula->r)) {
                    throw VariableFreeError(formula->r, formula->l->l->s);
                }
    //                        for (Node *v : supposes) {
    //                            if (checkVarIsFreeInFormula(formula->l->l->s, v)) {
    //                                throw VariableFreeError(v, formula->l->l->s);
    //                            }
    //                        }

                Node *A = alpha;
                Node *B = formula->l->r;
                Node *C = formula->r;
                vector<Node*> tmpSupposes;
                vector<Node*> tmpFormulas;
                vector<Node*> tmpProof;

                /// A->B->C |- B->A->C
                /// A->B->C, B, A |- C ...
                tmpSupposes.push_back(new Node("->", A, new Node("->", B, C)));
                tmpSupposes.push_back(B);

                tmpFormulas.push_back(A);
                tmpFormulas.push_back(B);
                tmpFormulas.push_back(tmpSupposes[0]);
                tmpFormulas.push_back(tmpFormulas.back()->r);
                tmpFormulas.push_back(tmpFormulas.back()->r);

                simpleDeduction(tmpFormulas, tmpSupposes, A, C, tmpProof);
                /// ... A->B->C, B |- A->C
                tmpSupposes.pop_back();

                simpleDeduction(tmpProof, tmpSupposes, B, new Node("->", A, C), proof);
                /// ... A->B->C |- B->(A->C)

                /// ?xB->(A->C)
                proof.push_back(new Node("->", formula->l, new Node("->", A, C)));
                ////////////////////////////////////////////////////
                /// ?xB->(A->C) |- A->(?xB->C)
                /// ?xB->(A->C), A, ?xB |- C ...
                tmpSupposes.clear();
                tmpFormulas.clear();
                tmpSupposes.push_back(proof.back());
                tmpSupposes.push_back(A);

                tmpFormulas.push_back(A);
                tmpFormulas.push_back(tmpSupposes[0]->l);
                tmpFormulas.push_back(tmpSupposes[0]);
                tmpFormulas.push_back(tmpFormulas.back()->r);
                tmpFormulas.push_back(tmpFormulas.back()->r);

                simpleDeduction(tmpFormulas, tmpSupposes, tmpSupposes[0]->l, C, tmpProof);
                /// ... ?xB->(A->C), A |- ?xB->C
                tmpSupposes.pop_back();
                simpleDeduction(tmpProof, tmpSupposes, A, formula, proof);
                /// ... A->(?xB->C)
                ////////////////////////////////////////////////////

            } else {
                type = 6;
                Node *v = checkIsModusPonens(formula, formulas);
                if (v != NULL) {
    //                    cout << "modus ponens" << "\n";
                    proof.push_back(getAxiom(2, alpha, v, formula));
                    proof.push_back(proof.back()->r);
                    proof.push_back(proof.back()->r);
                } else {
    //                    cout << "uknown stuff" << "\n";
                    throw UnknownError();
                }
            }
        }
    } catch (const SubstituteError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "терм " << e.x->getAsString()
             << " не свободен для подстановки в формулу " << e.y->getAsString()
             << " вместо переменной " << e.a << ".\n";
    } catch (const VariableFreeError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "переменная " << e.a << " входит свободно в формулу " << e.x->getAsString() << ".\n";
    } catch (const KvantorError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ": ";
        cout << "используется " << e.type << " с квантором по переменной " << e.a
             << ", входящей свободно в допущение " << e.x->getAsString() << ".\n";
    } catch (const UnknownError &e) {
        cout << "Вывод некорректен начиная с формулы " << counter << ".\n";
    } catch (const char *c) {
        cout << c << "\n";
    }

        /*} catch (const SubstituteError &e) {
            cout << "Вывод некорректен начиная с формулы " << counter << ": ";
            cout << "терм " << e.x->getAsString()
                 << " не свободен для подстановки в формулу " << e.y->getAsString()
                 << " вместо переменной " << e.a << ".\n";
        } catch (const VariableFreeError &e) {
            cout << "Вывод некорректен начиная с формулы " << counter << ": ";
            cout << "переменная " << e.a << " входит свободно в формулу " << e.x->getAsString() << ".\n";
        } catch (const KvantorError &e) {
            cout << "Вывод некорректен начиная с формулы " << counter << ": ";
            cout << "используется " << e.type << " с квантором по переменной " << e.a
                 << ", входящей свободно в допущение " << e.x->getAsString() << ".\n";
        } catch (const UnknownError &e) {
            cout << "Вывод некорректен начиная с формулы " << counter << ".\n";
        } catch (const char *c) {
            cout << c << "\n";
        }*/

}

Node *setAllKvantor(Node *v, string s) {
    return new Node("->", v->l, new Node("@", new Node(s, NULL, NULL), v->r));
}

Node *renameVars(vector<Node *> &proof, Node *a, string oldA, Node *newA
    , string oldB, Node *newB , string oldC, Node *newC) {

    proof.push_back(CONST);
    proof.push_back(a);
    proof.push_back(getAxiom(1, a, CONST));
    proof.push_back(proof.back()->r);
    proof.push_back(setAllKvantor(proof.back(), oldC));
    proof.push_back(setAllKvantor(proof.back(), oldB));
    proof.push_back(setAllKvantor(proof.back(), oldA));
    proof.push_back(proof.back()->r);

    bool tmp = true;
    Node *sub = substitute(proof.back()->r, oldA, newA, tmp);
    proof.push_back(new Node("->", proof.back(), sub));
    proof.push_back(proof.back()->r);

    tmp = true;
    sub = substitute(proof.back()->r, oldB, newB, tmp);
    proof.push_back(new Node("->", proof.back(), sub));
    proof.push_back(proof.back()->r);

    tmp = true;
    sub = substitute(proof.back()->r, oldC, newC, tmp);
    proof.push_back(new Node("->", proof.back(), sub));
    proof.push_back(proof.back()->r);

    return proof.back();
}

#endif // NODEPARSER_H
