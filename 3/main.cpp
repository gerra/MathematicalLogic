#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <map>

using namespace std;

const int N = 5000;

long long prime[N * N];

string getStringWithoutSpaces(const string & s) {
    string res = "";
    for (unsigned int i = 0; i < s.length(); i++) {
        char c = s[i];
        if (!isspace(c)) res += c;
    }
    return res;
}

bool isVariable(const string& s) {
    if (s.length() > 0 && s[0] >= 'A' && s[0] <= 'Z') {
        return true;
    }
    return false;
}

struct Node {
    long long hash;
    int vertCnt;
    int ptrCnt;
    bool lastValue;
    string s;
    Node * l;
    Node * r;
    Node() : vertCnt(0), ptrCnt(0), l(NULL), r(NULL) {}
    Node(string s, Node * l, Node * r) : s(s), l(l), r(r) {
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
        hash *= prime[1];
        hash += s[0];
        if (r) {
            hash *= prime[rCnt];
            hash += r->hash;
            r->ptrCnt++;
        }

    }
    ~Node() {
        if (l && l->ptrCnt == 0) delete l;
        if (r && r->ptrCnt == 0) delete r;
    }
    string getAsString(bool isMain = true) {
        string result = "";
        if (!isVariable(s) && !isMain) {
            result += "(";
        }
        if (l) {
            result += l->getAsString(false);
        }
        result += s;
        if (r) {
            result += r->getAsString(false);
        }
        if (!isVariable(s) && !isMain) {
            result += ")";
        }
        return result;
    }

    bool eval(const map<string, bool> &values) {
        if (isVariable(s)) {
            auto it = values.find(s);
            if (it == values.end()) throw "There is no this value in map";
            lastValue = it->second;
            return lastValue;
        }
        bool leftValue;
        bool rightValue;
        if (l) leftValue = l->eval(values);
        if (r) rightValue = r->eval(values);
        if (s == "->") {
            return lastValue = rightValue | !leftValue;
        } else if (s == "|") {
            return lastValue = leftValue | rightValue;
        } else if (s == "&") {
            return lastValue = leftValue & rightValue;
        } else if (s == "!") {
            return lastValue = !rightValue;
        }
    }

    void getVariables(map<string, bool> &values) {
        if (isVariable(s)) {
            values[s] = false;
            return;
        }
        if (l) l->getVariables(values);
        if (r) r->getVariables(values);
    }
};

Node *notX(Node *x) {
    return new Node("!", NULL, x);
}

Node *notNotX(Node *x) {
    return notX(notX(x));
}

Node *axioms[10];

bool checkEqualHard(Node * a, Node * b) {
    if (!a && !b) return true;
    if (!a || !b) return false;
    if (a->s != b->s) return false;
    if (!checkEqualHard(a->l, b->l)) return false;
    if (!checkEqualHard(a->r, b->r)) return false;
    return true;
}

// TODO: for 3 Nodes
// a != NULL && b != NULL
bool checkEqual(Node * a, Node * b) {
    if (a->hash != b->hash) return false;
    return checkEqualHard(a, b);
}

Node * parseTitle();
Node * parseExpression(const string &s, int &ptr);
Node * parseDisjuction(const string &s, int &ptr);
Node * parseConjuction(const string &s, int &ptr);
Node * parseUnary(const string &s, int &ptr);
void getAA(Node *a, vector<Node*> &proof);

Node * parseUnary(const string &s, int &ptr) {
    char c = s[ptr];
    if (c >= 'A' && c <= 'Z') {
        string name;
        name += c;
        ptr++;
        while (ptr < s.length() && s[ptr] >= '0' && s[ptr] <= '9') {
            name += s[ptr++];
        }
        return new Node(name, NULL, NULL);
    } else if (c == '!') {
        ptr++;
        Node * expr = parseUnary(s, ptr);
        return notX(expr);
    } else if (c == '(') {
        ptr++;
        Node * expr = parseExpression(s, ptr);
        if (ptr >= s.length() || s[ptr++] != ')') {
            throw ") doesn't exist";
        }
        return expr;
    }
    throw "incorrect formula";
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
    return parseExpression(s, ptr);
}


void Print(Node * v, ostream & fout) {
    if (v) {
        fout << v->getAsString();
    }
}

bool fillMap(Node * formula, Node * template_, map<string, vector<Node *> > &variableMap) {
    if (formula == NULL && template_ == NULL) {
        return true;
    }
    if (formula == NULL || template_ == NULL) {
        return false;
    }
    if (formula == template_) {
        return true;
    }
    const string &tempStr = template_->s;
    if (isVariable(tempStr)) {
        variableMap[tempStr].push_back(formula);
        return true;
    } else {
        if (tempStr != formula->s) {
            return false;
        }
        return fillMap(formula->l, template_->l, variableMap) &&
                fillMap(formula->r, template_->r, variableMap);
    }
}

bool checkFormulaIsSimilarToTemplate(Node * formula, Node * template_) {
    map<string, vector<Node*> > variableMap;
    if (fillMap(formula, template_, variableMap)) {
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

int checkItIsAxiom(Node * v) {
    for (int i = 0; i < 10; i++) {
        if (checkFormulaIsSimilarToTemplate(v, axioms[i])) {
            return i + 1;
        }
    }
    return -1;
}

bool checkItIsSuppose(Node * expr, const vector<Node *> & supposes, int begin_ = 0, int end_ = -1) {
    if (end_ == -1) {
        end_ = supposes.size();
    }
    for (unsigned int i = begin_; i < end_; i++) {
        if (checkEqual(expr, supposes[i])) {
            return true;
        }
    }
    return false;
}

pair<int, int> checkModusPonens(const vector<Node*> &formulas, int id, int begin_ = 0) {
    for (int i = id - 1; i >= begin_; i--) {
        Node * AB = formulas[i];
        if (AB && AB->s == "->" && AB->r && formulas[id] && checkEqual(AB->r, formulas[id])) {
            for (int j = 0; j < id; j++) {
                Node * A = formulas[j];
                if (A && AB->l && checkEqual(A, AB->l)) {
                    return make_pair(j, i);
                }
            }
        }
    }
    return make_pair(-1, -1);
}

void init() {
    prime[0] = 1;
    prime[1] = 31;
    for (int i = 2; i < N * N; i++) {
        prime[i] = prime[i - 1] * prime[1];
    }
    axioms[0] = parseStringToFormula("A->B->A");
    axioms[1] = parseStringToFormula("(A->B)->(A->B->C)->(A->C)");
    axioms[2] = parseStringToFormula("A->B->A&B");
    axioms[3] = parseStringToFormula("A&B->A");
    axioms[4] = parseStringToFormula("A&B->B");
    axioms[5] = parseStringToFormula("A->A|B");
    axioms[6] = parseStringToFormula("B->A|B");
    axioms[7] = parseStringToFormula("(A->C)->(B->C)->(A|B->C)");
    axioms[8] = parseStringToFormula("(A->B)->(A->!B)->!A");
    axioms[9] = parseStringToFormula("!!A->A");
}

Node *getFormulaFromTemplate(Node *v, Node *a, Node *b, Node *c) {
    if (!v) return NULL;
    if (v->s == "A") return a;
    if (v->s == "B") return b;
    if (v->s == "C") return c;
    return new Node(v->s,
                    getFormulaFromTemplate(v->l, a, b, c),
                    getFormulaFromTemplate(v->r, a, b, c));
}

Node *getAxiom(int axiomNumber, Node *a = NULL, Node *b = NULL, Node *c = NULL) {
    axiomNumber--;
    return getFormulaFromTemplate(axioms[axiomNumber], a, b, c);
}

void deduction(
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
        int axiomNumber = checkItIsAxiom(expr);
        int proofStart = proof.size();
        if (axiomNumber != -1 || checkItIsSuppose(expr, supposes, supBegin_, supEnd_)) {
            // di
            proof.push_back(expr);
            // di -> (a -> di)
            proof.push_back(getAxiom(1, expr, alpha));
            proof.push_back(proof.back()->r);
        } else if (checkEqual(expr, alpha)) {
            getAA(alpha, proof);
        } else {
            pair<int, int> mp = checkModusPonens(formulas, i, forBegin_);
            if (mp.first != -1) {
                Node * dj = formulas[mp.first];
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

void totalDeduction(const vector<Node*> &startFormulas, const vector<Node*> &supposes, const Node *firstBetta, vector<Node*> &proof) {
    Node *betta = new Node(firstBetta->s, firstBetta->l, firstBetta->r);
    vector<Node*> formulas(startFormulas);
    for (int i = supposes.size() - 1; i >= 0; i--) {
        vector<Node*> tempResult;
        deduction(formulas, supposes, supposes[i], betta, (i == 0 ? proof : tempResult), 0, i);
        formulas = tempResult;
        betta = new Node("->", supposes[i], betta);
    }
}

// α → β → (¬β → ¬α)
void getContraPositive(Node *a, Node *b, vector<Node*> &proof) {
    /*
        α → β, ¬β |- ¬α.
        (2) α → β Допущение
        (1) (α → β) → (α → ¬β) → ¬α Сх. акс. 9
        (3) (α → ¬β) → ¬α M.P. 2,1
        (4) ¬β → (α → ¬β) Сх. акс. 1
        (5) ¬β Допущение
        (6) α → ¬β M.P. 5,4
        (7) ¬α M.P. 6,3
    */
    vector<Node*> supposes;
    vector<Node*> formulas;
    supposes.push_back(new Node("->", a, b));
    supposes.push_back(notX(b));
    formulas.push_back(supposes[0]);
    formulas.push_back(getAxiom(9, a, b));
    formulas.push_back(formulas.back()->r);
    formulas.push_back(getAxiom(1, notX(b), a));
    formulas.push_back(supposes[1]);
    formulas.push_back(new Node("->", a, notX(b)));
    formulas.push_back(notX(a));
    totalDeduction(formulas, supposes, notX(a), proof);
}

void getThird(Node *a, vector<Node*> &proof) {
    /*1. Для начала покажем ` ¬(α ∨ ¬α) → ¬α:
    (1) α → α ∨ ¬α Сх. акс. 6
    (2). . .(n + 1) γ1, . . . γn−1,(α → α ∨ ¬α) → (¬(α ∨ ¬α) → ¬α) Д-во из леммы 4.4
    (n + 2) ¬(α ∨ ¬α) → ¬α M.P. 1,n + 1
    */
    proof.push_back(getAxiom(6, a, notX(a)));
    getContraPositive(a, new Node ("|", a, notX(a)), proof);
    proof.push_back(proof.back()->r);
    /*
    2. Затем докажем ` ¬(α ∨ ¬α) → ¬¬α:
    (1) ¬α → α ∨ ¬α Сх. акс. 7
    (2). . .(k + 1) δ1, . . . δk−1,(¬α → α ∨ ¬α) → (¬(α ∨ ¬α) → ¬¬α) Д-во из леммы 4.4
    (k + 2) ¬(α ∨ ¬α) → ¬¬α M.P. 1,k + 1
    */
    proof.push_back(getAxiom(7, a, notX(a)));
    getContraPositive(notX(a), new Node ("|", a, notX(a)), proof);
    proof.push_back(proof.back()->r);
    /*
    3. Теперь докажем все вместе:
    (1) ¬(α ∨ ¬α) → ¬α по пункту 1
    (2) ¬(α ∨ ¬α) → ¬¬α по пункту 2
    (3) (¬(α ∨ ¬α) → ¬α) → (¬(α ∨ ¬α) → ¬¬α) → (¬¬(α ∨ ¬α)) Сх. акс. 9
    (4) (¬(α ∨ ¬α) → ¬¬α) → ¬¬(α ∨ ¬α) M.P. 1,3
    (5) ¬¬(α ∨ ¬α) M.P. 2,4
    (6) ¬¬(α ∨ ¬α) → (α ∨ ¬α) Сх. акс. 10
    (7) α ∨ ¬α M.P. 5,6
    */
    proof.push_back(getAxiom(9, notX(new Node("|", a, notX(a))), notX(a)));
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
    proof.push_back(getAxiom(10, new Node("|", a, notX(a))));
    proof.push_back(proof.back()->r);
}

void getAA(Node *a, vector<Node*> &proof) {
    proof.push_back(getAxiom(1, a, a));
    proof.push_back(getAxiom(1, a, new Node("->", a, a)));
    proof.push_back(getAxiom(2, a, new Node("->", a, a), a));
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
}

void getAllVariableVariantes(vector<map<string, bool> > &variantes, Node *expr) {
    map<string, bool> variables;
    expr->getVariables(variables);
    vector<string> variablesNames;
    for (auto &it : variables) {
        variablesNames.push_back(it.first);
    }
    for (int mask = 0; mask < (1 << variables.size()); mask++) {
        variantes.push_back(map<string, bool>());
        expr->getVariables(variantes.back());
        for (int bit = 0; bit < variablesNames.size(); bit++) {
            variantes.back()[variablesNames[bit]] = ((mask & (1 << bit)) != 0 ? true : false);
        }
    }
}

void getSuppose(const map<string, bool> &values, vector<Node*> &suppose) {
    for (auto &x : values) {
        suppose.push_back(new Node(x.first, NULL, NULL));
        if (!x.second) {
            suppose.back() = notX(suppose.back());
        }
    }
}

void implFF(Node *a, Node *b, vector<Node*> &proof) {
    vector<Node*> tmp;
    tmp.push_back(notX(a));
    tmp.push_back(notX(b));
    tmp.push_back(a);
    tmp.push_back(getAxiom(1, a, notX(b)));
    tmp.push_back(tmp.back()->r);
    tmp.push_back(getAxiom(1, notX(a), notX(b)));
    tmp.push_back(tmp.back()->r);
    tmp.push_back(getAxiom(9, notX(b), a));
    tmp.push_back(tmp.back()->r);
    tmp.push_back(tmp.back()->r);
    tmp.push_back(getAxiom(10, b));
    tmp.push_back(tmp.back()->r);
    vector<Node*> sup;
    sup.push_back(notX(a));
    sup.push_back(notX(b));
    deduction(tmp, sup, a, b, proof);
}

void makeDerivation(Node *expr, vector<Node*> &proof, const map<string, bool> &values, bool firstTime = true) {
    if (firstTime) {
        expr->eval(values);
    }

    if (isVariable(expr->s) || checkItIsAxiom(expr) != -1) {
        proof.push_back(expr);
        if (!expr->lastValue) {
            proof.back() = notX(proof.back());
        }
        return;
    }

    if (expr->s == "|") {
        Node *a = expr->l;
        Node *b = expr->r;

        if (a->lastValue) {
            makeDerivation(a, proof, values, false);
            if (!isVariable(a->s)) proof.push_back(a);
            proof.push_back(getAxiom(6, a, b));
            proof.push_back(proof.back()->r);
        } else if (b->lastValue) {
            makeDerivation(b, proof, values, false);
            if (!isVariable(b->s)) proof.push_back(b);
            proof.push_back(getAxiom(7, a, b));
            proof.push_back(proof.back()->r);
        } else {
            makeDerivation(notX(a), proof, values, false);
            makeDerivation(notX(b), proof, values, false);
            if (!isVariable(a->s)) proof.push_back(notX(a));
            if (!isVariable(b->s)) proof.push_back(notX(b));
            proof.push_back(getAxiom(1, notX(a), expr));
            proof.push_back(proof.back()->r);


            getAA(a, proof);
            implFF(b, a, proof);
            proof.push_back(getAxiom(8, a, b, a));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);
            proof.push_back(getAxiom(9, expr, a));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);

//            vector<Node*> sup;
//            sup.push_back(notX(a));
//            sup.push_back(notX(b));
//            vector<Node*> tmp;
//            tmp.push_back(notX(a));
//            tmp.push_back(notX(b));
//            tmp.push_back(expr);
//            getAA(a, tmp);
//            implFF(b, a, tmp);
//            tmp.push_back(getAxiom(8, a, b, a));
//            tmp.push_back(tmp.back()->r);
//            tmp.push_back(tmp.back()->r);
//            tmp.push_back(tmp.back()->r);
//            deduction(tmp, sup, expr, a, proof);

//            proof.push_back(getAxiom(9, expr, a));
//            proof.push_back(proof.back()->r);
//            proof.push_back(proof.back()->r);
        }
    } else if (expr->s == "&") {
        Node *a = expr->l;
        Node *b = expr->r;
        if (a->lastValue && b->lastValue) {
            makeDerivation(a, proof, values, false);
            makeDerivation(b, proof, values, false);
            if (!isVariable(a->s)) proof.push_back(a);
            if (!isVariable(b->s)) proof.push_back(b);
            proof.push_back(getAxiom(3, a, b));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);
        } else if (a->lastValue && !b->lastValue) {
            makeDerivation(notX(b), proof, values, false);
            proof.push_back(getAxiom(5, a, b));
            if (!isVariable(b->s)) proof.push_back(notX(b));
            proof.push_back(getAxiom(1, notX(b), new Node("&", a, b)));
            proof.push_back(proof.back()->r);
            proof.push_back(getAxiom(9, new Node("&", a, b), b));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);
        } else {
            makeDerivation(notX(a), proof, values, false);
            proof.push_back(getAxiom(4, a, b));
            if (!isVariable(a->s)) proof.push_back(notX(a));
            proof.push_back(getAxiom(1, notX(a), new Node("&", a, b)));
            proof.push_back(proof.back()->r);
            proof.push_back(getAxiom(9, new Node("&", a, b), a));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);
        }
    } else if (expr->s == "->") {
        Node *a = expr->l;
        Node *b = expr->r;

        if (b->lastValue) {
            makeDerivation(b, proof, values, false);
            if (!isVariable(b->s)) proof.push_back(b);
            proof.push_back(getAxiom(1, b, a));
            proof.push_back(proof.back()->r);
        } else if (!a->lastValue && !b->lastValue) {
            makeDerivation(notX(a), proof, values, false);
            makeDerivation(notX(b), proof, values, false);
            implFF(a, b, proof);
        } else if (a->lastValue && !b->lastValue) {
            makeDerivation(a, proof, values, false);
            makeDerivation(notX(b), proof, values, false);
            if (!isVariable(a->s)) proof.push_back(a);
            if (!isVariable(b->s)) proof.push_back(notX(b));
            proof.push_back(getAxiom(1, notX(b), expr));
            proof.push_back(proof.back()->r);

            vector<Node*> sup;
            sup.push_back(a);
            sup.push_back(notX(b));
            vector<Node*> tmp;
            tmp.push_back(a);
            tmp.push_back(expr);
            tmp.push_back(b);
            deduction(tmp, sup, expr, b, proof);

            proof.push_back(getAxiom(9, expr, b));
            proof.push_back(proof.back()->r);
            proof.push_back(proof.back()->r);
        }
    } else if (expr->s == "!") {
        if (expr->r->s == "!") {
            Node *a = expr->r->r;
            if (a->lastValue) {
                makeDerivation(a, proof, values, false);
                if (!isVariable(a->s)) proof.push_back(a);
                proof.push_back(getAxiom(1, a, notX(a)));
                proof.push_back(proof.back()->r);
                getAA(notX(a), proof);
                proof.push_back(getAxiom(9, notX(a), a));
                proof.push_back(proof.back()->r);
                proof.push_back(proof.back()->r);
            } else {
                makeDerivation(notX(a), proof, values, false);
                if (!isVariable(a->s)) proof.push_back(notX(a));
            }
        } else {
            makeDerivation(expr->r, proof, values, false);
        }
    }
}

void exclude(const vector<Node*> &supposes, int supBegin, int supEnd,
             Node *p, Node *a,
             const vector<Node*> &formulas1, const vector<Node*> &formulas2,
             vector<Node*> &proof) {

    deduction(formulas1, supposes, notX(p), a, proof, supBegin, supEnd);
    deduction(formulas2, supposes, p, a, proof, supBegin, supEnd);

    getThird(p, proof);
    proof.push_back(getAxiom(8, p, notX(p), a));
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
}

int main() {
    init();
    ifstream in("input.txt");
    ofstream fout("output.txt");
    vector<Node*> supposes;
    vector<Node*> proof;
    vector<Node*> formulas;
    string s;

    try {
        getline(in, s);
        Node *expr = parseStringToFormula(s);

        vector<map<string, bool> > variableVariantes;
        getAllVariableVariantes(variableVariantes, expr);

        for (auto &it : variableVariantes) {
            if (!expr->eval(it)) {
                fout << "Высказывание ложно при ";
                for (auto var = it.begin(); var != it.end(); ++var) {
                    fout << var->first << "=" << (var->second ? "И" : "Л");
                    fout << (++var == it.end() ? "\n" : ", ");
                    --var;
                }
                return 0;
            }
        }

        vector<vector<Node*> > prooves(variableVariantes.size());
        vector<vector<Node*> > supposes(variableVariantes.size());

        for (int i = 0; i < variableVariantes.size(); i++) {
            getSuppose(variableVariantes[i], supposes[i]);
            makeDerivation(expr, prooves[i], variableVariantes[i]);
        }

        int varCnt = variableVariantes.begin()->size();
        int supStep = 2;
        int const totalCnt = varCnt;

        while (varCnt != 0) {
            vector<vector<Node*> > newProoves;
            for (int i = 0, curSupInd = 0; i < prooves.size(); i += 2, curSupInd += supStep) {
                vector<Node*> newProof;
                int curIndP = totalCnt - varCnt;
                exclude(
                            supposes[curSupInd],
                            curIndP + 1,
                            totalCnt,
                            supposes.back()[curIndP],
                            expr,
                            prooves[i],
                            prooves[i + 1],
                            newProof
                        );
                newProoves.push_back(newProof);
            }
            prooves = newProoves;
            varCnt--;
            supStep *= 2;
        }
        proof = prooves.back();

        int c = 0;
        for (Node *v : proof) {
            c++;
            fout << v->getAsString() << "\n";
        }
        cout << "Finish, " << c << " steps" << "\n";
    } catch (char const * err) {
        cerr << err << " in " << s << "\n";
    } catch (...) {
        cerr << "something wrong" << " in " << s << "\n";
    }
    return 0;
}
