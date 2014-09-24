#include <fstream>
#include <iostream>
#include <string>
#include <vector>

using namespace std;

const int N = 5000;

int n, ptr;
string s;
long long prime[N * N];

string getStringWithoutSpaces(const string & s) {
    string res = "";
    for (unsigned int i = 0; i < s.length(); i++) {
        char c = s[i];
        if (!isspace(c)) res += c;
    }
    return res;
}

void init() {
    prime[0] = 1;
    prime[1] = 31;
    for (int i = 2; i < N * N; i++)
        prime[i] = prime[i - 1] * prime[1];
}

struct Node {
    long long hash;
    int vertCnt;
    int ptrCnt;
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
            r->ptrCnt++;
        }

    }
    ~Node() {
        if (l && l->ptrCnt == 0) delete l;
        if (r && r->ptrCnt == 0) delete r;
    }
};

Node * formulas[N];

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

Node * parseTitle();
Node * parseExpression();
Node * parseDisjuction();
Node * parseConjuction();
Node * parseNegation();

Node * parseNegation() {
    char c = s[ptr];
    if (c >= 'A' && c <= 'Z') {
        string name;
        name += c;
        ptr++;
        if (ptr < n && s[ptr] >= '0' && s[ptr] <= '9') {
            name += s[ptr++];
        }
        return new Node(name, NULL, NULL);
    } else if (c == '!') {
        ptr++;
        Node * expr = parseNegation();
        return new Node("!", NULL, expr);
    } else if (c == '(') {
        ptr++;
        Node * expr = parseExpression();
        if (ptr >= n || s[ptr++] != ')') {
            throw ") doesn't exist";
        }
        return expr;
    }
    throw "incorrect formula";
}

Node * parseConjuction() {
    Node * expr = parseNegation();
    while (ptr < n && s[ptr] == '&') {
        ptr++;
        Node * expr2 = parseNegation();
        expr = new Node("&", expr, expr2);
    }
    return expr;
}

Node * parseDisjuction() {
    Node * expr = parseConjuction();
    while (ptr < n && s[ptr] == '|') {
        ptr++;
        Node * expr2 = parseConjuction();
        expr = new Node("|", expr, expr2);
    }
    return expr;
}

Node * parseExpression() {
    Node * expr1 = parseDisjuction();
    if (ptr < n && s[ptr] == '-' && s[++ptr] == '>') {
        ptr++;
        Node * expr2 = parseExpression();
        return new Node("->", expr1, expr2);
    }
    return expr1;
}

void parseTitle(const string & title, vector<Node *> & supposes, Node *& alpha, Node *& betta) {
    for (unsigned int i = 0; i < title.length(); ) {
        s.clear();
        ptr = 0;
        while (i < title.length() && title[i] != ',' && title[i] != '|') {
            s += title[i];
            i++;
        }
        n = s.length();
        Node * expr = parseExpression();
        if (title[i] == ',') {
            i++;
            supposes.push_back(expr);
        } else if (title[i] == '|'){
            i += 2;
            alpha = expr;
        } else {
            betta = expr;
        }
    }
}

void Print(Node * v, ostream & fout, bool isMain = true) {
    if (!v) return;
    bool isVariable = v->s[0] >= 'A' && v->s[0] <= 'Z';
    if (!isVariable && !isMain) {
        fout << "(";
    }
    Print(v->l, fout, false);
    fout << v->s;
    Print(v->r, fout, false);
    if (!isVariable && !isMain) {
        fout << ")";
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

// (A->C)->(B->C)->(A|B->C)
bool checkEighth(Node * v) {
    if (v && v->s == "->" && v->l && v->l->s == "->" && v->r && v->r->s == "->") {
        if (v->r->l && v->r->l->s == "->" && v->r->r && v->r->r->s == "->" &&
                v->r->r->l && v->r->r->l->s == "|") {
            if (v->l->l && v->l->r && v->r->l->l && v->r->l->r && v->r->r->r &&
                    v->r->r->l->l && v->r->r->l->r) {
                return (checkEqual(v->l->l, v->r->r->l->l) &&
                       checkEqual(v->r->l->l, v->r->r->l->r) &&
                       checkEqual(v->l->r, v->r->l->r));
            }
        }
    }
    return false;
}

// (A->B)->(A->!B)->!A
bool checkNinth(Node * v) {
    if (v && v->s == "->" && v->l && v->l->s == "->" && v->r && v->r->s == "->") {
        if (v->r->l && v->r->l->s == "->" && v->r->l->r && v->r->l->r->s == "!" &&
                v->r->r && v->r->r->s == "!") {
            if (v->l->l && v->r->l->l && v->r->r->r && v->l->r && v->r->l->r->r) {
                return (checkEqual(v->l->l, v->r->l->l) && checkEqual(v->l->l, v->r->r->r) &&
                       checkEqual(v->l->r, v->r->l->r->r));
            }
        }
    }
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

bool checkItIsSuppose(Node * expr, vector<Node *> & supposes) {
    for (unsigned int i = 0; i < supposes.size(); i++) {
        if (checkEqual(expr, supposes[i])) {
            return true;
        }
    }
    return false;
}

pair<int, int> checkModusPonens(int id) {
    for (int i = id - 1; i >= 0; i--) {
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

int main() {
    init();
    ifstream in("input.txt");
    ofstream out("output.txt");
    string title;
    vector<Node *> supposes;
    Node * alpha;
    Node * betta;
    try {
        getline(in, title);
        title = getStringWithoutSpaces(title);
        parseTitle(title, supposes, alpha, betta);
    } catch (char const * c) {
        cerr << c << " in " << title << "\n";
    } catch (...) {
        cerr << "something wrong...\n";
    }

    int counter = 1;
    while (getline(in, s)) {
        s = getStringWithoutSpaces(s);
        ptr = 0;
        n = s.length();
        if (n == 0) break;
        //out << "(" << counter << ") " << s;
        try {
            Node * expr = parseExpression();
            formulas[counter - 1] = expr;
            int axiomNumber = checkItIsAxiom(expr);
            Node * tmp;
            if (axiomNumber != -1 || checkItIsSuppose(expr, supposes)) {
                out << "1:\n";
                // di
                Print(expr, out); out << "\n";
                // di -> (a -> di)
                tmp = new Node("->", expr, new Node("->", alpha, expr));
                Print(tmp, out); out << "\n";
                delete tmp;
            } else if (checkEqual(expr, alpha)) {
                out << "2:\n";
                // a -> (a -> a)
                tmp = new Node("->", alpha, new Node("->", alpha, alpha));
                Print(tmp, out); out << "\n";
                delete tmp;
                // (a -> (a -> a)) -> (a -> ((a -> a) -> a)) -> (a -> a)
                tmp = new Node("->",
                               new Node("->", alpha, new Node("->", alpha, alpha)),
                               new Node("->", new Node("->", alpha,
                                                 new Node ("->",
                                                           new Node("->", alpha, alpha),
                                                           alpha)),
                                        new Node("->", alpha, alpha)));
                Print(tmp, out); out << "\n";
                delete tmp;
                // (a -> ((a -> a) -> a)) -> (a -> a)
                tmp =  new Node("->",
                                new Node("->", alpha,
                                        new Node ("->", new Node("->", alpha, alpha),
                                                  alpha)),
                                new Node("->", alpha, alpha));
                Print(tmp, out); out << "\n";
                delete tmp;
                // a -> ((a -> a) -> a)
                tmp = new Node("->", alpha,
                               new Node ("->", new Node("->", alpha, alpha), alpha));
                Print(tmp, out); out << "\n";
                delete tmp;
            } else {
                out << "3:\n";
                pair<int, int> mp = checkModusPonens(counter - 1);
                if (mp.first != -1) {
                    Node * dj = formulas[mp.first];
                    //Node * dk = formulas[mp.second];
                    // (a -> dj) -> ((a -> (dj -> di))) -> (a -> di)
                    tmp = new Node("->", new Node("->", alpha, dj),
                                   new Node("->", new Node("->", alpha,
                                                           new Node("->", dj, expr)),
                                            new Node("->", alpha, expr)));
                    Print(tmp, out); out << "\n";
                    delete tmp;
                    // ((a -> (dj -> di))) -> (a -> di)
                    tmp = new Node("->", new Node("->", alpha,
                                                  new Node("->", dj, expr)),
                                   new Node("->", alpha, expr));
                    Print(tmp, out); out << "\n";
                    delete tmp;
                } else {
                    throw "there is an error in proof";
                }
            }
            tmp = new Node("->", alpha, expr);
            Print(tmp, out); out << "\n";
            delete tmp;
        } catch (char const * err) {
            cerr << err << " in " << s << "\n";
        } catch (...) {
            cerr << "something wrong" << " in " << s << "\n";
        }
        counter++;
    }
    return 0;
}
