#include <fstream>
#include <iostream>
#include <string>
#include <map>
#include <vector>
#include <stdio.h>

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

struct Node {
    long long hash;
    int vertCnt;
    string s;
    Node * l;
    Node * r;
    Node() : hash(0), l(NULL), r(NULL) {}
    Node(string s, Node * l, Node * r) : s(s), l(l), r(r) {
        vertCnt = 1;
        int lCnt = 0, rCnt = 0;
        if (l) {
            lCnt  = l->vertCnt;
            vertCnt += lCnt;
        }
        if (l) {
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
        }

    }
    ~Node() {
        if (l) delete l;
        if (r) delete r;
    }
};

bool isVariable(const string& s) {
    if (s.length() > 0 && s[0] >= 'A' && s[0] <= 'Z') {
        return true;
    }
    return false;
}

Node * formulas[N*N], * axioms[10];
bool wasProofed[N*N];

bool checkEqualHard(Node * a, Node * b) {
    if (!a && !b) return true;
    if (!a || !b) return false;
    if (a->s != b->s) return false;
    if (!checkEqualHard(a->l, b->l)) return false;
    if (!checkEqualHard(a->r, b->r)) return false;
    return true;
}

bool checkEqual(Node * a, Node * b) {
    if (!a && !b) {
        return true;
    }
    if (!a || !b) {
        return false;
    }
    if (a == b) {
        return true;
    }
    if (a->hash != b->hash) return false;
    return checkEqualHard(a, b);
}

Node * parseExpression(const string &s, int &ptr);
Node * parseDisjuction(const string &s, int &ptr);
Node * parseConjuction(const string &s, int &ptr);
Node * parseNegation(const string &s, int &ptr);

Node * parseNegation(const string &s, int &ptr) {
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
        Node * expr = parseNegation(s, ptr);
        return new Node("!", NULL, expr);
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
    Node * expr = parseNegation(s, ptr);
    while (ptr < s.length() && s[ptr] == '&') {
        ptr++;
        Node * expr2 = parseNegation(s, ptr);
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

void Print(Node * v) {
    if (v->l) {
        cout << "(";
        Print(v->l);
        cout << ")";
    }
    cout << v->s;
    if (v->r) {
        cout << "(";
        Print(v->r);
        cout << ")";
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

pair<int, int> checkModusPonens(int id) {
    for (int i = id - 1; i >= 0; i--) {
        if (!wasProofed[i]) continue;
        Node * AB = formulas[i];
        if (AB && AB->s == "->" && AB->r && formulas[id] && checkEqual(AB->r, formulas[id])) {
            for (int j = 0; j < id; j++) {
                if (!wasProofed[j]) continue;
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

int main() {
    init();
    ifstream in("input.txt");
    ofstream out("output.txt");
    int counter = 1;
    string s;
    while (getline(in, s)) {
        s = getStringWithoutSpaces(s);
        if (s.length() == 0) break;
        out << "(" << counter << ") " << s;
        try {
            Node * expr = parseStringToFormula(s);
            formulas[counter - 1] = expr;
            int axiomNumber = checkItIsAxiom(expr);
            if (axiomNumber != -1) {
                out << " (Сх. акс. " << axiomNumber << ")\n";
                wasProofed[counter - 1] = true;
            } else {
                pair<int, int> mp = checkModusPonens(counter - 1);
                if (mp.first != -1) {
                    out << " (M.P. " << mp.first + 1 << ", " << mp.second + 1 << ")\n";
                    wasProofed[counter - 1] = true;
                } else {
                    out << " (Не доказано)\n";
                    return 0;
                }
            }
        } catch (char const * err) {
            out << err << " in " << s << "\n";
        } catch (...) {
            out << "something wrong...\n";
        }
        counter++;
    }
    return 0;
}
