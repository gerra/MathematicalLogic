#include "NodeParser.h"
#include <iostream>
#include <fstream>
#include <set>
#include <algorithm>

using namespace std;

struct World {
    set<std::string> forcedVars;

    World() {}
    World(const World &other) {
        forcedVars.insert(other.forcedVars.begin(), other.forcedVars.end());
    }

    void forceVar(const std::string &var) {
        forcedVars.insert(var);
    }

    bool checkVarIsForced(const string &var) const {
        return forcedVars.find(var) != forcedVars.end();
    }

    set<std::string> getForcedVars() const {
        return forcedVars;
    }

    void print(ostream &out) const {
        out << "* ";
        for (auto &var : forcedVars) {
            out << var << " ";
        }
        out << "\n";
    }

    bool isSubsetOf(const World &other) {
        for (auto &var : forcedVars) {
            if (other.getForcedVars().find(var) == other.getForcedVars().end()) {
                return false;
            }
        }
        return true;
    }
};

struct Tree;
vector<Tree*> allTrees;

struct Tree {
    World world;
    vector<Tree *> trees;
    int posInArray, childId;
    bool exist;

    Tree() {
        exist = true;
    }
    Tree(const World &world) {
        this->world = World(world);
        exist = true;
    }
    Tree(const Tree &other) {
        trees.clear();
        for (auto &world : other.trees) {
            trees.push_back(world);
        }
        world = World(other.world);
        exist = true;
    }

    World getWorld() {
        return world;
    }

    void addWorld(const World &world) {
        childId = trees.size();
        trees.push_back(new Tree(world));
        posInArray = allTrees.size();
        allTrees.push_back(trees.back());
    }

    bool checkFormula(Node *formula) {
        if (!exist) return true;
        if (formula->isPredicate()) {
            return world.checkVarIsForced(formula->s);
        }
        if (formula->s == "|") {
            return checkFormula(formula->l) || checkFormula(formula->r);
        } else if (formula->s == "&") {
            return checkFormula(formula->l) && checkFormula(formula->r);
        } else if (formula->s == "!") {
            if (checkFormula(formula->r)) {
                return false;
            }
            for (auto *world : trees) {
                if (world->exist && world->checkFormula(formula->r)) {
                    return false;
                }
            }
            return true;
        } else if (formula->s == "->") {
            if (checkFormula(formula->l) && !checkFormula(formula->r)) {
                return false;
            }
            for (auto *world : trees) {
                if (world->exist && world->checkFormula(formula->l) && !world->checkFormula(formula->r)) {
                    return false;
                }
            }
            return true;
        }
    }

    void print(ostream &out, int shift = 0) {
        if (exist) {
            for (int i = 0; i < shift; i++) out << ' ';
            world.print(out);
            for (auto *tree : trees) {
                tree->print(out, shift + 2);
            }
        } else {
            return;
        }
    }
};

bool operator < (const World &world1, const World &world2) {
    return world1.getForcedVars().size() < world2.getForcedVars().size();
}

void generateWorlds(World curWorld, vector<World> &worlds, set<string>::iterator curVar, int pos) {
    if (pos == 0) {
        worlds.push_back(curWorld);
        return;
    }
    World newWorld1(curWorld);
    ++curVar;
    generateWorlds(newWorld1, worlds, curVar, pos - 1);

    --curVar;
    World newWorld2(curWorld);
    newWorld2.forceVar(*curVar);
    ++curVar;
    generateWorlds(newWorld2, worlds, curVar, pos - 1);

    sort(worlds.begin(), worlds.end());
}

vector<World> generateWorlds(Node *formula) {
    set<string> vars = formula->getVars();

    vector<World> worlds;

    generateWorlds(World(), worlds, vars.begin(), vars.size());
    return worlds;
}

void generateTrees(Tree *curKripke, vector<World> &worlds) {
    for (int i = 1; i < worlds.size(); i++) {
        if (curKripke->getWorld() < worlds[i] && curKripke->getWorld().isSubsetOf(worlds[i])) {
            curKripke->addWorld(worlds[i]);
            generateTrees(curKripke->trees.back(), worlds);
        }
    }
//    for (auto *tree : curKripke->trees) {
//          generateTrees(tree, worlds);
//    }
}

bool check(Node *formula, int pos) {
    if (pos == allTrees.size()) {
        bool result = allTrees[0]->checkFormula(formula);
        return result;
    }
    allTrees[pos]->exist = true;
    if (!check(formula, pos+1)) {
        return false;
    }
    allTrees[pos]->exist = false;

//    if (!check(formula, pos+1)) {
//        return false;
//    }

    int nxt = allTrees[pos]->childId + 1;
    if (nxt < allTrees[pos]->trees.size()) {
        nxt = allTrees[pos]->trees[nxt]->posInArray;
    } else {
        nxt = pos+1;
    }
    if (!check(formula, nxt)) {
        return false;
    }
    return true;
}

void generateTrees(vector<World> &worlds) {
    Tree *bigTree = new Tree();
    allTrees.push_back(bigTree);
    generateTrees(bigTree, worlds);
}

int main() {
    ifstream cin("input5.in");
//    ofstream cout("output5.out");
    try {
        string s;
        getline(cin, s);
//        Node *formula = parseStringToFormula("(P->Q->R)|(!P->Q->R)|!(Q->R)");
//        Node *formula = parseStringToFormula("!!(!!P->P)");
//        Node *formula = parseStringToFormula("A|!A");
//        Node *formula = parseStringToFormula("(((P->Q)->P)->P)");
//        Node *formula = parseStringToFormula("((P->Q)&(Q->P))|((P->R)&(R->P))|((Q->R)&(R->Q))");
        Node *formula = parseStringToFormula(s);

        vector<World> worlds = generateWorlds(formula);
        generateTrees(worlds);

        if (!check(formula, 0)) {
            cout << "Контрмодель:\n";
            allTrees[0]->print(cout);
        } else {
            cout << "Формула общезначима\n";
        }
    } catch (const char *e) {
        cout << e << "\n";
    }
    return 0;
}