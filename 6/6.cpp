#include <iostream>
#include <fstream>
#include <vector>
#include "NodeParser.h"

using namespace std;

#define MP(a) (a.push_back(a.back()->r))
#define EX_AX(a, var) (new Node("->", a, new Node("?", var, a)))
#define FA_AX
#define EX_RULE(a, var) (new Node("->", new Node("?", var, a->l), a->r))

string emptyVar = "a000000";

void incEmptyVar() {
    int x = 0;
    for (int i = 1; i < emptyVar.length(); i++) {
        x = x * 10 + (emptyVar[i] - '0');
    }
    x++;
    if (x == 1000000) {
        x = 0;
        emptyVar[0]++;
    }
    for (int i = emptyVar.length() - 1; i > 0; i--) {
        emptyVar[i] = (x % 10 + '0');
        x /= 10;
    }
}

// ?xA(x) |- ?x1A(x1)
Node *renameExist(Node *alpha, vector<Node *> &proof, bool addFormulaToProof = true) {
    if (addFormulaToProof) {
        proof.push_back(alpha);
    }
    Node *oldVar = alpha->l;
    Node *newVar = new Node(emptyVar, NULL, NULL);
    Node *Ax1 = substitute(alpha->r, oldVar->s, newVar);
    Node *toProof = new Node("?", newVar, Ax1);
    proof.push_back(new Node("->", alpha->r, toProof));
    proof.push_back(new Node("->", alpha, toProof));
    MP(proof);
    incEmptyVar();
    return proof.back();
}

// @xA(x) -> @x1A(x1)
Node *renameForall(Node *alpha, vector<Node *> &proof, string x1) {
    Node *oldVar = alpha->l;
    Node *newVar = new Node(x1, NULL, NULL);
    Node *Ax1 = substitute(alpha->r, oldVar->s, newVar);
    Node *toProof = new Node("@", newVar, Ax1);
    proof.push_back(new Node("->", alpha, Ax1));
    proof.push_back(new Node("->", alpha, toProof));
    return proof.back();
}

// (A&?x(B(x))) -> ?x(A&B(x))
void rule1(Node *alpha, vector<Node *> &proof) {
    Node *f = alpha->l;
    Node *s = alpha->r;     // ?x(B(x))
    Node *b = alpha->r->r;  // (B(x))
    Node *var = alpha->r->l; // x
    Node *toProofWith = new Node("?", var, new Node("&", f, b));

    vector<Node *> tmpProof1;
    vector<Node *> tmpSupposes1;
    tmpProof1.push_back(alpha);
    tmpProof1.push_back(getAxiom(4, f, s));
    MP(tmpProof1);
    tmpProof1.push_back(getAxiom(5, f, s));
    MP(tmpProof1);

    vector<Node *> tmpProof2;
    vector<Node *> tmpSupposes2;
    tmpSupposes2.push_back(f);
    tmpProof2.push_back(f);
    tmpProof2.push_back(b);
    tmpProof2.push_back(getAxiom(3, f, b));
    MP(tmpProof2);
    MP(tmpProof2);
    tmpProof2.push_back(EX_AX(new Node("&", f, b), var));
    MP(tmpProof2);
    simpleDeductionFormal(tmpProof2, tmpSupposes2, b, toProofWith, tmpProof1);

    tmpProof1.push_back(EX_RULE(tmpProof1.back(), var));
    MP(tmpProof1);
    simpleDeductionFormal(tmpProof1, tmpSupposes1, alpha, toProofWith, proof);
}

// ?xA(x)&B -> ?x(A(x)&B)

// (A|?x(B(x))) -> ?x(A|B(x))

// ?xA(x)|B -> ?x(A(x)|B)

void deleteExist(const vector<Node *> &supposes, Node *alpha, Node *betta, vector<Node *> &proof) {

}

// ?xA, A->A1 |- ?xA1
void makeEqualExist(Node *formula, Node *a1, vector<Node *> &proof) {
    vector<Node *> tmpProof;
    vector<Node *> tmpSupposes;

    Node *a = formula->r;
    Node *predA = new Node("?", formula->l, a1);
    tmpSupposes.push_back(proof.back());
    tmpProof.push_back(a);
    tmpProof.push_back(tmpSupposes.back());
    MP(tmpProof);
    tmpProof.push_back(new Node("->", a1, predA));
    MP(tmpProof);
    simpleDeductionFormal(tmpProof, tmpSupposes, a, predA, proof);  /// A(x) -> ?xA1(x)
    proof.push_back(new Node("->", formula, predA));
    MP(proof);
}

Node *renameAllKvantors(Node *formula, vector<Node *> &proof, bool addFormulaToProof = true) {
    if (addFormulaToProof) {
        proof.push_back(formula);
    }
    if (formula->s == "?") {
        vector<Node *> tmpProof;
        vector<Node *> tmpSupposes;
        Node *renamed = renameAllKvantors(formula->r, tmpProof);
        simpleDeductionFormal(tmpProof, tmpSupposes, formula->r, renamed, proof);
        makeEqualExist(formula, renamed, proof);
        return renameExist(proof.back(), proof, false);
    } else if (formula->s == "!") {

    } else {
        return formula;
    }
}

Node *makePred(Node *formula, vector<Node *> &proof, bool addFormulaToProof = true) {
    if (addFormulaToProof) {
        proof.push_back(formula);
    }
    if (formula->isPredvar) {
        //cout << formula->getAsString() << "\n";
        Node *renamed = renameAllKvantors(formula, proof, false);
        //cout << proof.back()->getAsString() << "\n";
        return renamed;
    }
    if (formula->s == "?") {
        Node *a = formula->r;

        vector<Node *> tmpProof;
        vector<Node *> tmpSupposes;

        Node *a1 = makePred(a, tmpProof);
        simpleDeductionFormal(tmpProof, tmpSupposes, a, a1, proof); /// A(x) -> A1(x)

        tmpProof.clear();
        tmpSupposes.clear();

        Node *predA = new Node("?", formula->l, a1);
        tmpSupposes.push_back(proof.back());
        tmpProof.push_back(a);
        tmpProof.push_back(tmpSupposes.back());
        MP(tmpProof);
        tmpProof.push_back(new Node("->", a1, predA));
        MP(tmpProof);
        simpleDeductionFormal(tmpProof, tmpSupposes, a, predA, proof);  /// A(x) -> ?xA1(x)
        proof.push_back(new Node("->", formula, predA));
        MP(proof);
        return renameExist(proof.back(), proof, false);
    } else if (formula->s == "|") {
        Node *a = formula->l;
        Node *b = formula->r;

        vector<Node *> tmpProof;
        vector<Node *> tmpSupposes;
        Node *a1 = makePred(a, tmpProof);

        for (Node *v : tmpProof) {
            cout << v->getAsString() << "\n";
        }

        simpleDeductionFormal(tmpProof, tmpSupposes, a, a1, proof); /// A -> A1

        Node *a_a1 = proof.back();

        tmpProof.clear();
        Node *b1 = makePred(b, tmpProof);
        simpleDeductionFormal(tmpProof, tmpSupposes, b, b1, proof); /// B -> B1
        Node *b_b1 = proof.back();

        Node *toProof = new Node("|", a1, b1);

        proof.push_back(getAxiom(6, a1, b1));
        proof.push_back(getAxiom(1, proof.back(), a));
        MP(proof);
        proof.push_back(getAxiom(2, a, a1, toProof));
        MP(proof);
        MP(proof);

        proof.push_back(getAxiom(7, a1, b1));
        proof.push_back(getAxiom(1, proof.back(), b));
        MP(proof);
        proof.push_back(getAxiom(2, b, b1, toProof));
        MP(proof);
        MP(proof);

        proof.push_back(getAxiom(8, a, b, toProof));
        MP(proof);
        MP(proof);
        MP(proof);
        return proof.back();
    } else {
        Node *renamed = renameVars(proof, formula, "x", new Node(emptyVar, NULL, NULL), "1", A, "1", A);
        return renamed;
    }
}

int main() {
    ofstream cout("out.txt");
    init();
    Node *A = CONST;
    Node *x = new Node("x", NULL, NULL);
    Node *xx = new Node("=", x, x);
    Node *B = getAxiom(1, xx, xx);

    Node *y = new Node("y", NULL, NULL);
    Node *yy = new Node("=", y, y);
    Node *C = getAxiom(1, yy, yy);

    Node *tmp = new Node("&", A, new Node("?", x, B));
    vector<Node *> proof;
    try {
        //rule1(tmp, proof);
        //MP(proof);
        //renameExist(proof.back(), proof, "x1");
        //MP(proof);
        //cout << ":: " << makePred(new Node("?", x, B), proof)->getAsString() << "\n";
        cout << ":: " << makePred(parseStringToFormula("?x(x=x)|?x(x=0)"), proof)->getAsString() << "\n";
        for (Node *v : proof) {
            cout << v->getAsString() << "\n";
        }
    } catch(char const *a) {
        cout << a << "\n";
    }

    return 0;
}
