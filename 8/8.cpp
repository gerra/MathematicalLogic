#include <iostream>
#include <fstream>
#include <list>
#include <stdlib.h>

using namespace std;

typedef long long LL;

string intToString(int x) {
    char buf[100];
    buf[1] = 0;
    buf[0] = '0' + x % 10;
    return string(buf);
}

struct Ordinal {
    Ordinal *f;
    Ordinal *s;
    LL atomValue;
    Ordinal (Ordinal *f = NULL, Ordinal *s = NULL) {
        this->f = f;
        this->s = s;
    }
    Ordinal (LL atomValue) : Ordinal() {
        this->atomValue = atomValue;
    }
    Ordinal (Ordinal *f, LL s) {
        this->f = f;
        this->s = new Ordinal(s);
    }
    string toString() {
        if (!f && !s) {
            return intToString(atomValue);
        }
        return "w^(" + f->f->toString() + ")*" + f->s->toString() + "+" + s->toString();
    }
};
Ordinal *nil = new Ordinal(0LL);
Ordinal *one = new Ordinal(1LL);
Ordinal *w = new Ordinal(new Ordinal(one, 1LL), 0LL);

Ordinal *first(const Ordinal *a) {
    return a->f;
}

Ordinal *rest(Ordinal *a) {
    return a->s;
}

Ordinal *firstn(Ordinal *a, int n) {
    if (n == 0) {
        return new Ordinal();
    } else {
        return new Ordinal(first(a), firstn(rest(a), n - 1));
    }
}

Ordinal *restn(Ordinal *a, int n) {
    if (n == 0) {
        return a;
    } else {
        return restn(rest(a), n - 1);
    }
}

bool atom(Ordinal *a) {
    if (!a->f && !a->s) {
        return true;
    }
    return false;
}

Ordinal *fe(Ordinal *a) {
    return atom(a) ? new Ordinal(0LL) : first(first(a));
}

Ordinal *fc(Ordinal *a) {
    return atom(a) ? a : rest(first(a));
}

int length(Ordinal *a) {
    if (atom(a)) {
        return 0;
    }
    return 1 + length(rest(a));
}

int sze(Ordinal *a) {
    return atom(a) ? 1 : sze(fe(a)) + sze(rest(a));
}

Ordinal *append(Ordinal *a, Ordinal *b) {
    return atom(a) ? b : new Ordinal(first(a), append(rest(a), b));
}

int cmpw(LL atomA, LL atomB) {
    if (atomA < atomB) return -1;
    if (atomA > atomB) return  1;
    return 0;
}

int cmpo(Ordinal *a, Ordinal *b) {
    if (atom(a) && atom(b)) {
        return cmpw(a->atomValue, b->atomValue);
    }
    if (atom(a)) return -1;
    if (atom(b)) return  1;
    int res = cmpo(fe(a), fe(b));
    if (res != 0) return res;
    res = cmpw(fc(a)->atomValue, fc(b)->atomValue);
    if (res != 0) return res;
    return cmpo(rest(a), rest(b));
}

bool cmp(Ordinal *a, Ordinal *b) {
    return cmpo(a, b) == -1;
}

/*bool cnfp(Ordinal *a) {
    if (atom(a)) return true;
    return !atom(first(a))
            && fc(a)->atomValue != -1 // ???
            && cmpw(0, fc(a)->atomValue) == -1
            && cnfp(fe(a))
            && cnfp(rest(a))
            && cmp(fe(rest(a)), fe(a));
}*/

Ordinal *pluso(Ordinal *a, Ordinal *b) {
    if (atom(a) && atom(b)) return new Ordinal(a->atomValue + b->atomValue);
    int cmpRes = cmpo(fe(a), fe(b));
    if (cmpRes == -1) return b;
    if (cmpRes == 0) return new Ordinal(new Ordinal(fe(a), new Ordinal(fc(a)->atomValue + fc(b)->atomValue)), rest(b));
    return new Ordinal(new Ordinal(fe(a), fc(a)), pluso(rest(a), b));
}

Ordinal *minuso(Ordinal *a, Ordinal *b) {
    if (atom(a) && atom(b) && a->atomValue <= b->atomValue) return new Ordinal(0LL);
    if (atom(a) && atom(b)) return new Ordinal(a->atomValue - b->atomValue);
    int cmpRes = cmpo(fe(a), fe(b));
    if (cmpRes == -1) return new Ordinal(0LL);
    if (cmpRes == 1) return a;
    cmpRes = cmpw(fc(a)->atomValue, fc(b)->atomValue);
    if (cmpRes == -1) return new Ordinal(0LL);
    if (cmpRes == 1) return new Ordinal(new Ordinal(fe(a), fc(a)->atomValue - fc(b)->atomValue), rest(a));
    return minuso(rest(a), rest(b));
}

int c(Ordinal *a, Ordinal *b) {
    if (cmp(fe(b), fe(a))) return 1 + c(rest(a), b);
    return 0;
}

int cAfterN(Ordinal *a, Ordinal *b, int n) {
    return n + c(restn(a, n), b);
}

Ordinal *padd(Ordinal *a, Ordinal *b, int n) {
    return append(firstn(a, n), pluso(restn(a, n), b));
}

Ordinal *pmult(Ordinal *a, Ordinal *b, int n) {
    if (atom(a) && a->atomValue == 0 || atom(b) && b->atomValue == 0) return new Ordinal(0LL);
    if (atom(a) && atom(b)) return new Ordinal(a->atomValue * b->atomValue);
    if (atom(b)) return new Ordinal(new Ordinal(fe(a), new Ordinal(fc(a)->atomValue * b->atomValue)), rest(a));
    int m = cAfterN(fe(a), fe(b), n);
    return new Ordinal(new Ordinal(padd(fe(a), fe(b), m), fc(b)), pmult(a, rest(b), m));
}

Ordinal *multo(Ordinal *a, Ordinal *b) {
    return pmult(a, b, 0);
}

LL expw(LL a, LL b) {
    LL res = 1;
    while (b) {
        if (b & 1) res *= a;
        a *= a;
        b /= 2;
    }
    return res;
}

/// int to power of infinity ordinal
Ordinal *exp1(LL p, Ordinal *b) {
    if (cmpo(fe(b), one) == 0) {
        return new Ordinal(new Ordinal(fc(b), expw(p, rest(b)->atomValue)), 0LL);
    }
    if (atom(rest(b))) {
        return new Ordinal(new Ordinal(new Ordinal(new Ordinal(minuso(fe(b), one), fc(b)), nil), expw(p, rest(b)->atomValue)), nil);
    }
    Ordinal *c = exp1(p, rest(b));
    return new Ordinal(new Ordinal(new Ordinal(new Ordinal(minuso(fe(b), one), one), fe(c)), fc(c)), nil);
}

/// limit ordinal to a positive power
Ordinal *exp2(Ordinal *a, LL q) {
    if (q == 1) return a;
    return multo(new Ordinal(new Ordinal(multo(fe(a), new Ordinal(q - 1)), 1LL), 0LL), a);
    //return multo(new Ordinal(new Ordinal(exp2(a, q-1), 1LL), 0LL), a);
}

bool limitp(Ordinal *a) {
    if (atom(a)) return a->atomValue == 0;
    return limitp(rest(a));
}

Ordinal *limitpart(Ordinal *a) {
    if (atom(a)) return nil;
    return new Ordinal(first(a), limitpart(rest(a)));
}

LL natpart(Ordinal *a) {
    if (atom(a)) return a->atomValue;
    return natpart(rest(a));
}

Ordinal *exp32(Ordinal *a, Ordinal *p, LL n, LL q) {
    if (q == 0) return p;
    return padd(multo(exp2(a, q), p), exp32(a, p, n, q - 1), n);
}

/// inf to int
Ordinal *exp3(Ordinal *a, LL q) {
    if (q == 0) return one;
    if (q == 1) return a;
    if (limitp(a)) return exp2(a, q);
   // Ordinal *c = limitpart(a);
   // int n = length(a);
   // return padd(firstn(exp2(c, q), exp32(c, natpart(a), n, q-1), n))
    return multo(exp3(a, q - 1), a);
}

Ordinal *exp4(Ordinal *a, Ordinal *b) {
    return multo(new Ordinal(new Ordinal(multo(fe(a), limitpart(b)), one), nil), exp3(a, natpart(b)));
}

Ordinal *expo(Ordinal *a, Ordinal *b) {
    if (cmpo(a, one) == 0 || cmpo(b, nil) == 0) return one;
    if (cmpo(a, nil) == 0) return nil;
    if (atom(a) && atom(b)) return new Ordinal(expw(a->atomValue, b->atomValue));
    if (atom(a)) return exp1(a->atomValue, b);
    if (atom(b)) return exp3(a, b->atomValue);
    return exp4(a, b);
}

Ordinal *parseExpression(const string&, int &);

Ordinal *parseTerm(const string &s, int &ptr) {
    if (s[ptr] == 'w') {
        ptr++;
        return w;
    }
    if (s[ptr] == '(') {
        ptr++;
        Ordinal *res = parseExpression(s, ptr);
        ptr++; // ')'
        return res;
    }
    LL x = 0;
    while (s[ptr] >= '0' && s[ptr] <= '9') {
        x = x * 10 + (s[ptr] - '0');
        ptr++;
    }
    return new Ordinal(x);
}

Ordinal *parseMul(const string &s, int &ptr) {
    Ordinal *res = parseTerm(s, ptr);
    if (ptr < s.length() && s[ptr] == '^') {
        ptr++;
        Ordinal *tmp  = parseMul(s, ptr);
        res = expo(res, tmp);
    }
    return res;
}

Ordinal *parseAdd(const string &s, int &ptr) {
    Ordinal *res = parseMul(s, ptr);
    while (ptr < s.length() && s[ptr] == '*') {
        ptr++;
        Ordinal *tmp = parseMul(s, ptr);
        res = multo(res, tmp);
    }
    return res;
}

Ordinal *parseExpression(const string &s, int &ptr) {
    Ordinal *res = parseAdd(s, ptr);
    while (ptr < s.length() && s[ptr] == '+') {
        ptr++;
        Ordinal *tmp = parseAdd(s, ptr);
        res = pluso(res, tmp);
    }
    return res;
}

Ordinal *parseStringToOrdinal(const string &s) {
    int ptr = 0;
    return parseExpression(s, ptr);
}

string getStringWithoutSpaces(const string & s) {
    string res = "";
    for (unsigned int i = 0; i < s.length(); i++) {
        char c = s[i];
        if (!isspace(c)) res += c;
    }
    return res;
}

/*
(w+1)^2=w^2+2*w+1
(w^2+2*w+11+w^w)^w=(w^2+2*w+11+w^w)^w
w^7*14+w^5*22+21=(w^5*22+21)*(w^2+1)*14
w*(((123+32+17)*43)^2)=w+w*(54700815)
w^(w^(w*15+1239)+w^w+w^(w^12))=(w*2)^(w^(w*15+1239)+w^(w^12))
w^((w+w+w)^2)*w^(w^3) = w^(w*w*w)
(w^2+2*w+11+w^w)^w=w^(w*w)
(w^2+2*w+11+w^w)^w=w^(w*w)
*/

/*
5=3
(w+1)^2=w^2+w*2+1
(w^((w+w+w)^w))*w^(w^3) = w^(w*w*w)
w^(w^(w*15+1239)+w^w+w^(w^12))=(w*2)^(w^(w*15+1239)+w^(w^12)+w^(w^12))
w*((((123+32+17)*43)^2)*2)=(w+w)*(54700815)
(w+1)^2=w^2+w*2+1
(w^2+1)*2=w^2*2+2
*/

int main() {
    ifstream cin("input8.txt");
    ofstream cout("output8.txt");
    string s;
    while (getline(cin, s)) {
        s = getStringWithoutSpaces(s);
        int i;
        for (i = 0; i < s.length(); i++) {
            if (s[i] == '=') break;
        }
        Ordinal *o1 = parseStringToOrdinal(s.substr(0, i));
        Ordinal *o2 = parseStringToOrdinal(s.substr(i+1));

        cout << (cmpo(o1, o2) == 0 ? "Равны" : "Не равны") << "\n";
    }
    return 0;
}
