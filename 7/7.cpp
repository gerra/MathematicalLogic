#include <iostream>
#include <fstream>
#include <vector>

using namespace std;

#include "NodeParser.h"

void simpleDeductionFormal(
        const vector<Node *> &formulas,
        const vector<Node *> &supposes,
        Node *alpha, Node *betta,
        vector<Node *> &proof) {

    for (Node *formula : formulas) {
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


Node *getNAsNode(int x) {
    Node *v = new Node("0", NULL, NULL);
    while (x--) {
        v = new Node("'", v, NULL);
    }
    return v;
}

Node *setAllKvantor(Node *v, string s) {
    return new Node("->", v->l, new Node("@", new Node(s, NULL, NULL), v->r));
}

Node *deleteAllKvantor(Node *v) {
    return v->r;
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

// a + 0 = a
void getAddAxiom1(Node *a, vector<Node *> &proof) {
    Node *newA = new Node ("a000", NULL, NULL);
    Node *newB = new Node ("b000", NULL, NULL);
    Node *newC = new Node ("c000", NULL, NULL);
    //proof.push_back(CONST);
    //proof.push_back(axioms[18]);
    Node *a18 = renameVars(proof, axioms[18], "a", newA, "b", newB, "c", newC);
    proof.push_back(getAxiom(1, a18, CONST));
    proof.push_back(proof.back()->r);
    proof.push_back(setAllKvantor(proof.back(), newA->s));
    proof.push_back(proof.back()->r);
    bool tmp = true;
    Node *sub = substitute(proof.back()->r, newA->s, a, tmp);
    proof.push_back(new Node("->", proof.back(), sub));
    proof.push_back(proof.back()->r);
}

// a + b' = (a + b)'
void getAddAxiom2(Node *a, Node *b, vector<Node *> &proof) {

}


// a * 0 = a
void getMulAxiom1(Node *a, vector<Node *> &proof) {

}

// a * b' = a * b + a
void getMulAxiom2(Node *a, Node *b, vector<Node *> &proof) {

}

// a=a
void getAEqA(vector<Node *> &proof) {
    Node *newA = new Node ("a004", NULL, NULL);
    Node *newB = new Node ("b004", NULL, NULL);
    Node *newC = new Node ("c004", NULL, NULL);

    Node *a18 = renameVars(proof, axioms[18], "a", newA, "b", newB, "c", newC);
    Node *a14 = renameVars(proof, axioms[14], "a", newA, "b", newB, "c", newC);
    //proof.push_back(CONST);
    //proof.push_back(axioms[18]);
    //proof.push_back(axioms[14]);
    proof.push_back(getAxiom(1, a14, CONST));
    proof.push_back(proof.back()->r);
    proof.push_back(setAllKvantor(proof.back(), newC->s));
    proof.push_back(setAllKvantor(proof.back(), newB->s));
    proof.push_back(setAllKvantor(proof.back(), newA->s));
    proof.push_back(proof.back()->r);
    bool tmp = true;
    Node *sub = substitute(proof.back()->r, newA->s, new Node("+", newA, NIL), tmp);
    proof.push_back(new Node("->", proof.back(), sub));
    proof.push_back(proof.back()->r);
    tmp = true;
    sub = substitute(proof.back()->r, newB->s, newA, tmp);
    proof.push_back(new Node("->", proof.back(), sub));
    proof.push_back(proof.back()->r);
    tmp = true;
    sub = substitute(proof.back()->r, newC->s, newA, tmp);
    proof.push_back(new Node("->", proof.back(), sub));
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
    proof.push_back(proof.back()->r);
}

// a005->b005|-b005->a005
void swapEqual(vector<Node *> &proof) {
    Node *newA = new Node ("a005", NULL, NULL);
    Node *newB = new Node ("b005", NULL, NULL);
    Node *newC = new Node ("c005", NULL, NULL);

    vector<Node*> tmpProof;
    vector<Node*> tmpSupposes;
    Node *alpha = new Node("=", newA, newB);
    tmpProof.push_back(alpha);
    //proof.push_back(CONST);
    Node *a14 = renameVars(tmpProof, axioms[14], "a", newA, "b", newB, "c", newC);
    getAEqA(tmpProof);
    renameVars(tmpProof, tmpProof.back(), "a004", newA, "b004", newB, "c004", newC);
    tmpProof.push_back(getAxiom(1, a14, CONST));
    tmpProof.push_back(tmpProof.back()->r);
    tmpProof.push_back(setAllKvantor(tmpProof.back(), newC->s));
    tmpProof.push_back(tmpProof.back()->r);
    bool tmp = true;
    Node *sub = substitute(tmpProof.back()->r, newC->s, newA, tmp);
    tmpProof.push_back(new Node("->", tmpProof.back(), sub));
    tmpProof.push_back(tmpProof.back()->r);
    tmpProof.push_back(tmpProof.back()->r);
    tmpProof.push_back(tmpProof.back()->r);

    simpleDeductionFormal(tmpProof, tmpSupposes, alpha, tmpProof.back(), proof);
}

// a006=b006->a006+c006=b006+c006
void getAddProperty(vector<Node *> &proof) {
    Node *newA = new Node ("a006", NULL, NULL);
    Node *newB = new Node ("b006", NULL, NULL);
    Node *newC = new Node ("c006", NULL, NULL);

    vector <Node *> tmpProof;
    Node *alpha = new Node("=", newA, newB);
    tmpProof.push_back(alpha);
    getAddAxiom1(newA, tmpProof);
    getAddAxiom1(newB, tmpProof);
    swapEqual(tmpProof);
    Node *swapped = tmpProof.back();
    renameVars(tmpProof, swapped, "a005", new Node("+", newA, NIL), "b005", newA, "c005", newC); // a+0=a->a=a+0
    tmpProof.push_back(tmpProof.back()->r);
    renameVars(tmpProof, swapped, "a005", new Node("+", newB, NIL), "b005", newB, "c005", newC); // a+0=a->a=a+0
    tmpProof.push_back(tmpProof.back()->r);
    renameVars(tmpProof, axioms[14], "a", newA, "b", newB, "c", new Node("+", newA, NIL));
    tmpProof.push_back(tmpProof.back()->r);
    tmpProof.push_back(tmpProof.back()->r);
    renameVars(tmpProof, swapped, "a005", newA, "b005", newB, "c005", newC);
    tmpProof.push_back(tmpProof.back()->r);
    renameVars(tmpProof, axioms[14], "a", newB, "b", new Node("+", newA, NIL), "c", new Node("+", newB, NIL));
    tmpProof.push_back(tmpProof.back()->r);
    tmpProof.push_back(tmpProof.back()->r);

    for (Node *v : tmpProof) {
        proof.push_back(v);
    }
}

void printProofBIsDivisorOfA(int a, int b) {
    Node *nil = getNAsNode(0);
    Node *aNode = getNAsNode(a);
    Node *bNode = getNAsNode(0);
    vector<Node *> proof;
    proof.push_back(new Node("=", new Node("*", aNode, bNode), nil));
    for (int i = 1; i <= b; i++) {
        Node *oldB = bNode;
        bNode = new Node("'", bNode, NULL);
        proof.push_back(new Node("=", new Node("*", aNode, bNode), new Node("+", new Node("*", oldB, aNode), aNode)));
        Node *tmp = proof.back()->r->l;
        //proof.push_back(new Node("=", proof.back(), ))
    }

    for (Node *v : proof) {
        cout << v->getAsString() << "\n";
    }
}

int main() {
    ofstream cout("out.txt");
    init();
    //Node *v = getNAsNode(5);
    //cout << v->getAsString() << "\n";
    //printProofBIsDivisorOfA(3, 2);
    vector<Node *> proof;
    //getAddAxiom1(new Node("b", NULL, NULL), proof);
    //getAEqA(proof);
    //swapEqual(proof);
    //getAddAxiom1(new Node("z", NULL, NULL), proof);
    //proof.push_back(new Node("=", A, A));
    //renameVars(proof, proof.back(), "a", "a1", "b", "b1", "c", "c1");
    getAddProperty(proof);
    for (Node *v : proof) {
        cout << v->getAsString() << "\n";
    }
    return 0;
}
