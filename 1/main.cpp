#include <fstream>
#include <iostream>
#include <string>

using namespace std;

const int N = 5000;

int n, ptr;
string s;
long long prime[N * N];

void init() {
    prime[0] = 1;
    prime[1] = 31;
    for (int i = 2; i < N * N; i++)
        prime[i] = prime[i - 1] * prime[1];
}

struct Node {
    long long hash;
    int vertCnt;
    string s;
    Node * l;
    Node * r;
    Node() : l(NULL), r(NULL) {}
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

Node * formulas[N];
bool wasProofed[N];

bool checkEqualHard(Node * a, Node * b) {
    if ((a->l && !b->l) || (!a->l && b->l)) return false;
    if ((a->r && !b->r) || (!a->r && b->r)) return false;
    if (a->s != b->s) return false;
    if (a->l && b->l && !checkEqualHard(a->l, b->l)) return false;
    if (a->r && b->r && !checkEqualHard(a->r, b->r)) return false;
    return true;
}

// TODO: for 3 Nodes
// a != NULL && b != NULL
bool checkEqual(Node * a, Node * b) {
    if (a->hash != b->hash) return false;
    return checkEqualHard(a, b);
}

Node * parseExpression();
Node * parseDisjuction();
Node * parseConjuction();
Node * parseNegation();

void deleteSpaces() {
    while (ptr < n && s[ptr] == ' ') {
        ptr++;
    }
}

Node * parseNegation() {
    deleteSpaces();
    char c = s[ptr];
    if (c >= 'A' && c <= 'Z') {
        string name;
        name += c;
        ptr++;
        deleteSpaces();
        if (ptr < n && s[ptr] >= '0' && s[ptr] <= '9') {
            name += s[ptr++];
            deleteSpaces();
        }
        return new Node(name, NULL, NULL);
    } else if (c == '!') {
        ptr++;
        deleteSpaces();
        Node * expr = parseNegation();
        deleteSpaces();
        return new Node("!", NULL, expr);
    } else if (c == '(') {
        ptr++;
        deleteSpaces();
        Node * expr = parseExpression();
        deleteSpaces();
        if (ptr >= n || s[ptr++] != ')') {
            throw ") doesn't exist";
        }
        return expr;
    }
    throw "incorrect formula";
}

Node * parseConjuction() {
    deleteSpaces();
    Node * expr = parseNegation();
    deleteSpaces();
    while (ptr < n && s[ptr] == '&') {
        ptr++;
        deleteSpaces();
        Node * expr2 = parseNegation();
        deleteSpaces();
        expr = new Node("&", expr, expr2);
    }
    return expr;
}

Node * parseDisjuction() {
    deleteSpaces();
    Node * expr = parseConjuction();
    deleteSpaces();
    while (ptr < n && s[ptr] == '|') {
        ptr++;
        deleteSpaces();
        Node * expr2 = parseConjuction();
        deleteSpaces();
        expr = new Node("|", expr, expr2);
    }
    return expr;
}

Node * parseExpression() {
    deleteSpaces();
    Node * expr1 = parseDisjuction();
    deleteSpaces();
    if (ptr < n && s[ptr] == '-' && s[++ptr] == '>') {
        ptr++;
        deleteSpaces();
        Node * expr2 = parseExpression();
        deleteSpaces();
        return new Node("->", expr1, expr2);
    }
    return expr1;
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

// A->B->A
bool checkFirst(Node * v) {
    if (v && v->s == "->" && v->r && v->r->s == "->") {
        return (v->l && v->r->r && checkEqual(v->l, v->r->r));
    }
    return false;
}
// (A->B)->(A->B->C)->(A->C)
bool checkSecond(Node * v) {
    if (v && v->s == "->" && v->l && v->l->s == "->" && v->r && v->r->s == "->") {
        if (v->r->l && v->r->l->s == "->" && v->r->r && v->r->r->s == "->") {
            if (v->r->l->r && v->r->l->r->s == "->") {
                if (v->l->l && v->l->r && v->r->l->l && v->r->l->r->l && v->r->l->r->r &&
                        v->r->r->l && v->r->r->r) {
                    return ((checkEqual(v->l->l, v->r->l->l) && checkEqual(v->r->r->l, v->l->l)) &&
                            (checkEqual(v->l->r, v->r->l->r->l)) &&
                            (checkEqual(v->r->r->r, v->r->l->r->r)));
                }
            }
        }
    }
    return false;
}

// A->B->A&B
bool checkThird(Node * v) {
    if (v && v->s == "->" && v->r && v->r->s == "->" && v->r->r && v->r->r->s == "&") {
        if (v->l && v->r->l && v->r->r->l && v->r->r->r) {
            return (checkEqual(v->l, v->r->r->l) && checkEqual(v->r->l, v->r->r->r));
        }
    }
    return false;
}

// A&B->A
bool checkFourth(Node * v) {
    if (v && v->s == "->" && v->l && v->l->s == "&") {
        if (v->l->l && v->l->r && v->r) {
            return checkEqual(v->l->l, v->r);
        }
    }
    return false;
}
// A&B->B
bool checkFifth(Node * v) {
    if (v && v->s == "->" && v->l && v->l->s == "&") {
        if (v->l->l && v->l->r && v->r) {
            return checkEqual(v->l->r, v->r);
        }
    }
    return false;
}
// A->A|B
bool checkSixth(Node * v) {
    if (v && v->s == "->" && v->r && v->r->s == "|") {
        if (v->l && v->r->l && v->r->r) {
          return checkEqual(v->l, v->r->l);
        }
    }
    return false;
}
// B->A|B
bool checkSeventh(Node * v) {
    if (v && v->s == "->" && v->r && v->r->s == "|") {
        if (v->l && v->r->l && v->r->r) {
            return checkEqual(v->l, v->r->r);
        }
    }
    return false;
}

bool checkEighth(Node * v) {
    return false;
}

bool checkNinth(Node * v) {
    return false;
}

// !!A->A
bool checkTenth(Node * v) {
    if (v && v->s == "->" && v->l && v->l->s == "!" && v->l->r && v->l->r->s == "!") {
        if (v->r && v->l->r->r) {
            return checkEqual(v->l->r->r, v->r);
        }
    }
    return false;
}

int checkItIsAxiom(Node * v) {
    if (checkFirst(v)) return 1;
    else if (checkSecond(v)) return 2;
    else if (checkThird(v)) return 3;
    else if (checkFourth(v)) return 4;
    else if (checkFifth(v)) return 5;
    else if (checkSixth(v)) return 6;
    else if (checkSeventh(v)) return 7;
    else if (checkEighth(v)) return 8;
    else if (checkNinth(v)) return 9;
    else if (checkTenth(v)) return 10;
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

int main() {
    init();
    ifstream in("input.txt");
    ofstream out("output.txt");
    int counter = 1;
    while (getline(in, s)) {
        ptr = 0;
        n = s.length();
        if (n == 0) break;
        cout << "(" << counter << ") " << s;
        try {
            Node * expr = parseExpression();
            formulas[counter - 1] = expr;
            int axiomNumber = checkItIsAxiom(expr);
            if (axiomNumber != -1) {
                cout << " (ax." << axiomNumber << ")\n";
                wasProofed[counter - 1] = true;
            } else {
                pair<int, int> mp = checkModusPonens(counter - 1);
                if (mp.first != -1) {
                    cout << " (M.P. " << mp.first + 1 << ", " << mp.second + 1 << ")\n";
                    wasProofed[counter - 1] = true;
                } else {
                    cout << " (can't be proofed)\n";
                }
            }
        } catch (char const * err) {
            cout << err << " in " << s << "\n";
        } catch (...) {
            cout << "something wrong...\n";
        }
        counter++;
    }
    return 0;
}
