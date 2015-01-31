#ifndef NODEPARSER_H
#define NODEPARSER_H

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

#endif // NODEPARSER_H
