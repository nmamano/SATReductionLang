#include <iostream>
#include <cctype>
#include <string>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <stack>
#include <cstdlib>
#include <sstream>
#include <fstream>
#include <cmath>
#include <queue>
#include <list>

#if defined(USE_MINISAT)
# include "core/Solver.h"
#elif defined(USE_PICOSAT)
extern "C" {
# include "picosat.h"
}
#else
# error "Define either USE_MINISAT or USE_PICOSAT"
#endif

using namespace std;

typedef long long int ll;

ll stollsat(string s)
{
  if (s.size() > 2 and s[0] == '{' and s[s.size() - 1] == '}')
    return stoll(s.substr(1, s.size() - 2));
  else
    return stoll(s);
}

string itos(ll x)
{
  if (x == 0) return "0";
  string s;
  bool signo = false;
  if (x < 0) {
    signo = true;
    x = -x;
  }
  while (x > 0) {
    s = string(1, char(x % 10 + '0')) + s;
    x /= 10;
  }
  if (signo)
    s = "-" + s;
  return s;
}

bool esentero(string s)
{
  for (int i = 0; i < int(s.size()); i++)
    if (not (s[i] >= '0' and s[i] <= '9'))
      return false;
  return true;
}

bool esletra(char c) {
  return (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z');
}

bool esnumero(char c) {
  return (c >= '0' and c <= '9');
}

bool esenterosat(string s)
{
  if (s.size() > 2 and s[0] == '{' and s[s.size() - 1] == '}')
    return esentero(s.substr(1, s.size() - 2));
  else
    return esentero(s);
}

void morirpuro(string mensajecortoingles, string mensajelargoingles,
               string mensajecortoespanyol, string mensajelargoespanyol,
               string mensajecortocatalan, string mensajelargocatalan)
{
  // Pendiente de saber los nombres de los ficheros.
  {
    ofstream corto("answer.eng");
    corto << mensajecortoingles << endl;
    corto.close();
    ofstream largo("answer.eng.long");
    largo << mensajelargoingles << endl;
    largo.close();
  }
  {
    ofstream corto("answer.esp");
    corto << mensajecortoespanyol << endl;
    corto.close();
    ofstream largo("answer.esp.long");
    largo << mensajelargoespanyol << endl;
    largo.close();
  }
  {
    ofstream corto("answer.cat");
    corto << mensajecortocatalan << endl;
    corto.close();
    ofstream largo("answer.cat.long");
    largo << mensajelargocatalan << endl;
    largo.close();
  }
  exit(0);
}

string prefijoerroringles, prefijoerrorespanyol, prefijoerrorcatalan;

void morir(string mensajecortoingles, string mensajelargoingles,
           string mensajecortoespanyol, string mensajelargoespanyol,
           string mensajecortocatalan, string mensajelargocatalan)
{
  morirpuro(mensajecortoingles, prefijoerroringles + mensajelargoingles,
            mensajecortoespanyol, prefijoerroringles + mensajelargoespanyol,
            mensajecortocatalan, prefijoerroringles + mensajelargocatalan);
}

void rechazar(string mensajelargoingles) {
  morir("rejected", mensajelargoingles, "rejected", mensajelargoingles, "rejected", mensajelargoingles);
}

void rechazar(int linea, int columna, string mensajelargoingles) {
  rechazar("Error line " + itos(linea) + " column " + itos(columna) + ": " + mensajelargoingles);
}

bool comando(string const &s)
{
  int const res = system(s.c_str());
  return (res != -1) and (WEXITSTATUS(res) == 0);
}

vector<string> leerfichero(string nombrefichero)
{
  vector<string> v;
  ifstream ifs;
  ifs.open(nombrefichero.c_str());
  if (ifs.is_open()) {
    string s;
    while (getline(ifs, s)) {
      for (int i = 0; i < int(s.size()); i++)
        if (s[i] == 13) s[i] = ' ';
      v.push_back(s);
    }
    ifs.close();
  } else {
    morir("rejected", "Error when opening " + nombrefichero,
          "rechazado", "Error al abrir " + nombrefichero,
          "rebutjat", "Error en obrir " + nombrefichero);
  }
  return v;
}


////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Analisis lexico del programa de entrada:


struct ttoken {
  string tipo, texto;
  int linea, columna;

  ttoken()
  {
  }
  ttoken(string intipo, string intexto, int inlinea, int incolumna)
  {
    tipo = intipo; texto = intexto, linea = inlinea, columna = incolumna;
  }
};


set<string> palabrasclave;
set<string> cadenasclave;

char listapalabrasclave[][80] = {"main", "in", "out", "stop",
                                 "if", "else", "while", "for", "foreach",
                                 "and", "or", "not", "push", "size",
                                 "back", "min", "max", "abs", "substr",
                                 "insertsat", ""
                                };

char listacadenasclave[][80] = {"{", "}", "(", ")", "[", "]", "+", "-", "*", "/", "%", "=", "&=", "==", "<",
                                ">", "<=", ">=", "!=", ";", ".", ",", "//", "++", "--", ""
                               };

void inicializartokensclave()
{
  for (int i = 0; string(listapalabrasclave[i]) != ""; i++)
    palabrasclave.insert(listapalabrasclave[i]);
  for (int i = 0; string(listacadenasclave[i]) != ""; i++)
    cadenasclave.insert(listacadenasclave[i]);
}

void leeridentificador(string &s, int &is, vector<ttoken> &vt, int linea)
{
  int nextis = is;
  while (nextis < int(s.size()) and
         ((s[nextis] >= 'a' and s[nextis] <= 'z') or
          (s[nextis] >= 'A' and s[nextis] <= 'Z') or
          (s[nextis] >= '0' and s[nextis] <= '9') or
          (s[nextis] == '_')))
    nextis++;
  string id = s.substr(is, nextis - is);
  if (palabrasclave.count(id))
    vt.push_back(ttoken(id, "", linea, is + 1));
  else
    vt.push_back(ttoken("identificador", id, linea, is + 1));
  is = nextis;
}

void leerconstante(string &s, int &is, vector<ttoken> &vt, int linea)
{
  int nextis = is;
  while (nextis<int(s.size()) and s[nextis] >= '0' and s[nextis] <= '9') nextis++;
  if (nextis - is >= 9)
    morir("rejected", "Error line " + itos(linea) + " column " + itos(is + 1) +
          ": the constant \"" + s.substr(is, nextis - is) + "\" is too big.\n" +
          "This does not mean that your reduction is wrong, but you should find a simpler one.",
          "rechazado", "Error linea " + itos(linea) + " columna " + itos(is + 1) +
          ": la constante \"" + s.substr(is, nextis - is) + "\" es demasiado grande.\n" +
          "Eso no significa que la reduccion este mal, pero si conviene buscar una reduccion mas sencilla.",
          "rebutjat", "Error linea " + itos(linea) + " columna " + itos(is + 1) +
          ": la constant \"" + s.substr(is, nextis - is) + "\" es massa gran.\n" +
          "Aixo no significa que la reduccio estigui malament, pero si conve buscar una solucio mes senzilla.");
  vt.push_back(ttoken("constante", s.substr(is, nextis - is), linea, is + 1));
  is = nextis;
}

void leerstring(string &s, int &is, vector<ttoken> &vt, int linea)
{
  int nextis = is + 1;
  while (nextis < int(s.size()) and s[nextis] != '"')
    nextis++;
  if (nextis == int(s.size()))
    morir("rejected", "Error line " + itos(linea) + " column " + itos(is + 1) +
          ": the string constant should end in this line with '\"'.",
          "rechazado", "Error linea " + itos(linea) + " columna " + itos(is + 1) +
          ": la constante string deberia terminar en esta misma linea con '\"'.",
          "rebutjat", "Error linea " + itos(linea) + " columna " + itos(is + 1) +
          ": la constant string hauria d'acabar en aquesta mateixa linia amb '\"'.");
  nextis++;
  vt.push_back(ttoken("string", s.substr(is + 1, nextis - is - 2), linea, is + 1));
  is = nextis;
}

void leertoken(string &s, int &is, vector<ttoken> &vt, int linea)
{
  if ((s[is] >= 'a' and s[is] <= 'z') or (s[is] >= 'A' and s[is] <= 'Z') or (s[is] == '_'))
    leeridentificador(s, is, vt, linea);
  else if (s[is] >= '0' and s[is] <= '9')
    leerconstante(s, is, vt, linea);
  else if (s[is] == '"')
    leerstring(s, is, vt, linea);
  else {
    set<string>::iterator it = cadenasclave.end();
    do {
      it--;
      string c = *it;
      if (int(s.size()) - is >= int(c.size()) and
          s.substr(is, int(c.size())) == c) {
        if (c == "//") {
          is = int(s.size());
          return;
        }
        vt.push_back(ttoken(c, "", linea, is + 1));
        is += int(c.size());
        return;
      }
    } while (it != cadenasclave.begin());
    morir("rejected", "Error line " + itos(linea) + " column " + itos(is + 1) +
          ": there is no correspondence for \"" + s.substr(is) + "\"",
          "rechazado", "Error linea " + itos(linea) + " columna " + itos(is + 1) +
          ": no se encuentra correspondencia para \"" + s.substr(is) + "\"",
          "rebutjat", "Error linea " + itos(linea) + " columna " + itos(is + 1) +
          ": no es troba correspondencia per a \"" + s.substr(is) + "\"");
  }
}

void saltarblancos(string &s, int &i)
{
  while (i < int(s.size()) and (s[i] == ' ' or s[i] == '\t')) i++;
}

void precompilarlinea(string &s)
{
  string nexts;
  bool comillas = false;
  for (int i = 0; i < int(s.size()); i++) {
    if (not comillas or (s[i] != '{' and s[i] != '}'))
      nexts += string(1, s[i]);
    //else if (s[i]=='<')
    //nexts+="\"+(";
    //else if (s[i]=='>')
    //nexts+=")+\"";
    else if (s[i] == '{')
      nexts += "{\"+(";
    else if (s[i] == '}')
      nexts += ")+\"}";
    if (s[i] == '"')
      comillas = not comillas;
  }
  s = nexts;
}

void leerentrada(string &s, vector<ttoken> &vt, int linea)
{
  int is = 0;
  saltarblancos(s, is);
  while (is < int(s.size())) {
    leertoken(s, is, vt, linea);
    saltarblancos(s, is);
  }
}

void leerentrada(vector<string> &vs, vector<ttoken> &vt)
{
  inicializartokensclave();
  for (int i = 0; i < int(vs.size()); i++) {
    precompilarlinea(vs[i]);
    leerentrada(vs[i], vt, i + 1);
  }
}

void verificarquenoseusa(string &t, vector<ttoken> &vt)
{
  for (int i = 0; i < int(vt.size()); i++)
    if (vt[i].tipo == t)
      morir("rejected", "Error line " + itos(vt[i].linea) + " column " + itos(vt[i].columna) +
            ": it is not allowed to use \"" + t + "\".",
            "rechazado", "Error linea " + itos(vt[i].linea) + " columna " + itos(vt[i].columna) +
            ": no se permite usar \"" + t + "\".",
            "rebutjat", "Error linea " + itos(vt[i].linea) + " columna " + itos(vt[i].columna) +
            ": no es permet usar \"" + t + "\".");
}

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Analisis sintactico del programa de entrada:


struct tnodo {
  string tipo, texto;
  int linea, columna;
  vector<tnodo> hijo;
  map<string, tnodo> m;
  tnodo() {
  }
  tnodo(string intipo, string intexto, int inlinea, int incolumna) {
    tipo = intipo; texto = intexto; linea = inlinea; columna = incolumna;
  }
  tnodo(string intipo, int inlinea, int incolumna) {
    tipo = intipo; texto = ""; linea = inlinea; columna = incolumna;
  }
  tnodo(ttoken token) {
    tipo = token.tipo; texto = token.texto; linea = token.linea; columna = token.columna;
  }

  vector<string> listacampos() {
    vector<string> res;
    for(auto x: m)
      res.push_back(x.first);
    return res;
  }
};

int limiteprofundidad = 10;

void controlarprofundidad(int profundidad, int linea, int columna)
{
  if (profundidad > limiteprofundidad)
    morir("rejected", "Error line " + itos(linea) + " column " + itos(columna) +
          ": the level of indexation is too big.",
          "rechazado", "Error linea " + itos(linea) + " columna " + itos(columna) +
          ": el nivel de indexacion es demasiado grande.",
          "rebutjat", "Error linea " + itos(linea) + " columna " + itos(columna) +
          ": el nivell d'indexacio es massa gran.");
}

void seesperabaver(vector<ttoken> &vt, int &ivt, string ingles, string espanyol, string catalan)
{
  if (ivt == int(vt.size()))
    morir("rejected", "Error: the end of the program was reached when"
          " we expected to see " + ingles + ".",
          "rechazado", "Error: se llego al final del programa cuando"
          " se esperaba ver " + espanyol + ".",
          "rebutjat", "Error: s'ha arribat al final del programa quan"
          " s'esperava veure " + catalan + ".");
  morir("rejected", string("Error line ") + itos(vt[ivt].linea) + " column " + itos(vt[ivt].columna) +
        ": we expected to see " + ingles + ", but we found \"" +
        vt[ivt].tipo + "\".",
        "rechazado", string("Error linea ") + itos(vt[ivt].linea) + " columna " + itos(vt[ivt].columna) +
        ": se esperaba ver " + espanyol + ", pero se encontro \"" +
        vt[ivt].tipo + "\".",
        "rebutjat", string("Error linea ") + itos(vt[ivt].linea) + " columna " + itos(vt[ivt].columna) +
        ": s'esperava veure " + catalan + ", pero es va trobar \"" +
        vt[ivt].tipo + "\".");
}

void seesperabaver(vector<ttoken> &vt, int &ivt, string t)
{
  seesperabaver(vt, ivt, t, t, t);
}

void saltartipo(vector<ttoken> &vt, int &ivt, string t)
{
  if (ivt == int(vt.size()) or vt[ivt].tipo != t)
    seesperabaver(vt, ivt, "\"" + t + "\"");
  ivt++;
}

void parsingexpresion(tnodo &nodo, vector<ttoken> &vt, int &ivt);

void parsingin(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  if (ivt == int(vt.size()) or (vt[ivt].tipo != "identificador" and vt[ivt].tipo != "in"))
    seesperabaver(vt, ivt, "{\"ident\",\"in\"}");
  nodo = vt[ivt];


  ivt++;
  int profundidad = 0;
  while (ivt < int(vt.size()) and (vt[ivt].tipo == "[" or vt[ivt].tipo == ".")) {
    profundidad++;
    controlarprofundidad(profundidad, vt[ivt].linea, vt[ivt].columna);
    if (vt[ivt].tipo == "[") {
      tnodo nodoaux = nodo;
      nodo = vt[ivt];
      nodo.hijo = vector<tnodo> (2);
      nodo.hijo[0] = nodoaux;
      ivt++;
      parsingexpresion(nodo.hijo[1], vt, ivt);
      saltartipo(vt, ivt, "]");
    } else {
      ivt++;
      if (ivt < int(vt.size()) and vt[ivt].tipo == "size") {
        tnodo nodoaux = nodo;
        nodo = vt[ivt];
        nodo.hijo = vector<tnodo> (1);
        nodo.hijo[0] = nodoaux;
        ivt++;
        break;
      } else if (ivt < int(vt.size()) and vt[ivt].tipo == "identificador") {
        tnodo nodoaux = nodo;
        nodo = vt[ivt];
        nodo.tipo = ".";
        nodo.hijo = vector<tnodo> (1);
        nodo.hijo[0] = nodoaux;
        ivt++;
      } else
        seesperabaver(vt, ivt, "{\"size\",\"ident\"}");
    }
  }
}

void parsingunarios(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  if (ivt == int(vt.size()))
    seesperabaver(vt, ivt, "{\"-\",\"not\",\"ident\",\"constant\",\"string\",\"(\",\"in\",\"out\",\"abs\",\"min\",\"max\"}");
  if (vt[ivt].tipo == "-" or vt[ivt].tipo == "not") {
    nodo = vt[ivt];
    nodo.hijo.push_back(tnodo());
    ivt++;
    parsingunarios(nodo.hijo[0], vt, ivt);
  } else if (vt[ivt].tipo == "constante" or vt[ivt].tipo == "string") {
    nodo = vt[ivt];
    ivt++;
  } else if (vt[ivt].tipo == "abs") {
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (1);
    ivt++;
    saltartipo(vt, ivt, "(");
    parsingexpresion(nodo.hijo[0], vt, ivt);
    saltartipo(vt, ivt, ")");
  } else if (vt[ivt].tipo == "substr" or vt[ivt].tipo == "max" or vt[ivt].tipo == "min") {
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (2);
    ivt++;
    saltartipo(vt, ivt, "(");
    parsingexpresion(nodo.hijo[0], vt, ivt);
    saltartipo(vt, ivt, ",");
    parsingexpresion(nodo.hijo[1], vt, ivt);
    saltartipo(vt, ivt, ")");
  } else if (vt[ivt].tipo == "(") {
    ivt++;
    parsingexpresion(nodo, vt, ivt);
    saltartipo(vt, ivt, ")");
  } else if (vt[ivt].tipo == "identificador" or vt[ivt].tipo == "in") {
    parsingin(nodo, vt, ivt);
  } else
    seesperabaver(vt, ivt, "{\"-\",\"not\",\"ident\",\"constant\",\"string\",\"(\",\"in\",\"out\",\"abs\",\"min\",\"max\"}");
}

void parsingmultiplicaciondivision(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  parsingunarios(nodo, vt, ivt);
  while (ivt < int(vt.size()) and (vt[ivt].tipo == "*" or vt[ivt].tipo == "/" or vt[ivt].tipo == "%")) {
    tnodo nodoaux = nodo;
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (2);
    nodo.hijo[0] = nodoaux;
    ivt++;
    parsingunarios(nodo.hijo[1], vt, ivt);
  }
}

void parsingsumasrestas(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  parsingmultiplicaciondivision(nodo, vt, ivt);
  while (ivt < int(vt.size()) and (vt[ivt].tipo == "+" or vt[ivt].tipo == "-")) {
    tnodo nodoaux = nodo;
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (2);
    nodo.hijo[0] = nodoaux;
    ivt++;
    parsingmultiplicaciondivision(nodo.hijo[1], vt, ivt);
  }
}

void parsingcomparaciones(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  parsingsumasrestas(nodo, vt, ivt);
  while (ivt < int(vt.size()) and
         (vt[ivt].tipo == "==" or vt[ivt].tipo == "<" or vt[ivt].tipo == ">"
          or vt[ivt].tipo == "<=" or vt[ivt].tipo == ">=" or vt[ivt].tipo == "!=")) {
    tnodo nodoaux = nodo;
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (2);
    nodo.hijo[0] = nodoaux;
    ivt++;
    parsingsumasrestas(nodo.hijo[1], vt, ivt);
  }
}

void parsingexpresion(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  parsingcomparaciones(nodo, vt, ivt);
  while (ivt < int(vt.size()) and (vt[ivt].tipo == "and" or vt[ivt].tipo == "or")) {
    tnodo nodoaux = nodo;
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (2);
    nodo.hijo[0] = nodoaux;
    ivt++;
    parsingcomparaciones(nodo.hijo[1], vt, ivt);
  }
}

void parsinglistainstrucciones(tnodo &nodo, vector<ttoken> &vt, int &ivt);

void parsingasignacionsimple(tnodo &nodo, vector<ttoken> &vt, int &ivt, string tipomarcafinal)
{
  if (ivt < int(vt.size()) and vt[ivt].tipo == tipomarcafinal) {
    nodo = vt[ivt];
    nodo.tipo = ";";
    ivt++;
  } else if (ivt < int(vt.size()) and vt[ivt].tipo == "identificador") {
    ttoken tokenid = vt[ivt];
    //string identificador=vt[ivt].texto;
    ivt++;
    if (ivt < int(vt.size()) and vt[ivt].tipo == "=") {
      nodo = vt[ivt];
      nodo.hijo = vector<tnodo> (2);
      nodo.hijo[0] = tokenid;
      ivt++;
      parsingexpresion(nodo.hijo[1], vt, ivt);
      saltartipo(vt, ivt, tipomarcafinal);
    } else if (ivt < int(vt.size()) and vt[ivt].tipo == "&=") {
      nodo = vt[ivt];
      nodo.hijo = vector<tnodo> (2);
      nodo.hijo[0] = tokenid;
      ivt++;
      parsingin(nodo.hijo[1], vt, ivt);
      saltartipo(vt, ivt, tipomarcafinal);
    } else if (ivt < int(vt.size()) and (vt[ivt].tipo == "++" or vt[ivt].tipo == "--")) {
      nodo = vt[ivt];
      nodo.hijo = vector<tnodo> (1);
      nodo.hijo[0] = tokenid;
      ivt++;
      saltartipo(vt, ivt, tipomarcafinal);
    } else
      seesperabaver(vt, ivt, "{\"=\",\"&=\",\"++\",\"--\"}");
  } else if (ivt < int(vt.size()) and (vt[ivt].tipo == "++" or vt[ivt].tipo == "--")) {
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (1);
    ivt++;
    if (ivt < int(vt.size()) and vt[ivt].tipo == "identificador") {
      nodo.hijo[0] = vt[ivt];
      ivt++;
      saltartipo(vt, ivt, tipomarcafinal);
    } else
      seesperabaver(vt, ivt, "\"ident\"");
  } else
    seesperabaver(vt, ivt, "{\"ident\",\"++\",\"--\",\"" + tipomarcafinal + "\"}");
}

void parsingout(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  if (ivt == int(vt.size()) or vt[ivt].tipo != "out")
    seesperabaver(vt, ivt, "\"out\"");
  nodo = vt[ivt];
  ivt++;
  int profundidad = 0;
  while (ivt < int(vt.size()) and (vt[ivt].tipo == "[" or vt[ivt].tipo == ".")) {
    profundidad++;
    controlarprofundidad(profundidad, vt[ivt].linea, vt[ivt].columna);
    if (vt[ivt].tipo == "[") {
      tnodo nodoaux = nodo;
      nodo = vt[ivt];
      nodo.hijo = vector<tnodo> (2);
      nodo.hijo[0] = nodoaux;
      ivt++;
      parsingexpresion(nodo.hijo[1], vt, ivt);
      saltartipo(vt, ivt, "]");
    } else {
      ivt++;
      if (ivt < int(vt.size()) and (vt[ivt].tipo == "push" or vt[ivt].tipo == "back")) {
        tnodo nodoaux = nodo;
        nodo = vt[ivt];
        nodo.hijo = vector<tnodo> (1);
        nodo.hijo[0] = nodoaux;
        ivt++;
      } else if (ivt < int(vt.size()) and vt[ivt].tipo == "identificador") {
        tnodo nodoaux = nodo;
        nodo = vt[ivt];
        nodo.tipo = ".";
        nodo.hijo = vector<tnodo> (1);
        nodo.hijo[0] = nodoaux;
        ivt++;
      } else
        seesperabaver(vt, ivt, "{\"push\",\"back\",\"ident\"}");
    }
  }
}

void parsinginstruccion(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  if (ivt == int(vt.size()))
    seesperabaver(vt, ivt, "{\"if\",\"ident\",\"++\",\"--\",\"{\",\"while\",\"for\",\"foreach\",\"out\",\"stop\"}");
  if (vt[ivt].tipo == "if") {
    nodo = vt[ivt];
    ivt++;
    saltartipo(vt, ivt, "(");
    nodo.hijo.push_back(tnodo());
    parsingexpresion(nodo.hijo[0], vt, ivt);
    saltartipo(vt, ivt, ")");
    nodo.hijo.push_back(tnodo());
    parsinginstruccion(nodo.hijo[1], vt, ivt);
    if (ivt < int(vt.size()) and vt[ivt].tipo == "else") {
      ivt++;
      nodo.hijo.push_back(tnodo());
      parsinginstruccion(nodo.hijo[2], vt, ivt);
    }
  } else if (vt[ivt].tipo == "insertsat") {
    nodo = vt[ivt];
    ivt++;
    saltartipo(vt, ivt, "(");
    if (ivt < int(vt.size()) and vt[ivt].tipo == "out") {
      nodo.hijo.push_back(tnodo());
      parsingout(nodo.hijo[0], vt, ivt);
      saltartipo(vt, ivt, ",");
    }
    nodo.hijo.push_back(tnodo());
    parsingexpresion(nodo.hijo.back(), vt, ivt);
    saltartipo(vt, ivt, ")");
    saltartipo(vt, ivt, ";");
  } else if (vt[ivt].tipo == "identificador" or vt[ivt].tipo == ";" or vt[ivt].tipo == "++" or vt[ivt].tipo == "--") {
    parsingasignacionsimple(nodo, vt, ivt, ";");
  } else if (vt[ivt].tipo == "out") {
    parsingout(nodo, vt, ivt);
    if (ivt < int(vt.size()) and vt[ivt].tipo == "=") {
      tnodo nodoaux = nodo;
      nodo = vt[ivt];
      nodo.tipo = "=,";
      nodo.hijo = vector<tnodo> (2);
      nodo.hijo[0] = nodoaux;
      ivt++;
      parsingexpresion(nodo.hijo[1], vt, ivt);
      while (ivt < int(vt.size()) and vt[ivt].tipo == ",") {
        ivt++;
        nodo.hijo.push_back(tnodo());
        parsingexpresion(nodo.hijo.back(), vt, ivt);
      }
    } else if (nodo.tipo != "push")
      seesperabaver(vt, ivt, "{\"=\",\".push\"}");
    saltartipo(vt, ivt, ";");
  } else if (vt[ivt].tipo == "while") {
    nodo = vt[ivt];
    ivt++;
    saltartipo(vt, ivt, "(");
    nodo.hijo.push_back(tnodo());
    parsingexpresion(nodo.hijo[0], vt, ivt);
    saltartipo(vt, ivt, ")");
    nodo.hijo.push_back(tnodo());
    parsinginstruccion(nodo.hijo[1], vt, ivt);
  } else if (vt[ivt].tipo == "foreach") {
    nodo = vt[ivt];
    ivt++;
    saltartipo(vt, ivt, "(");
    if (ivt == int(vt.size()) or vt[ivt].tipo != "identificador")
      seesperabaver(vt, ivt, "\"ident\"");
    nodo.hijo.push_back(vt[ivt]);
    ivt++;
    if (ivt < int(vt.size()) and vt[ivt].tipo == ",") {
      ivt++;
      if (ivt == int(vt.size()) or vt[ivt].tipo != "identificador")
        seesperabaver(vt, ivt, "\"ident\"");
      nodo.hijo.push_back(vt[ivt]);
      ivt++;
    }
    saltartipo(vt, ivt, ";");
    nodo.hijo.push_back(tnodo());
    parsingin(nodo.hijo.back(), vt, ivt);
    saltartipo(vt, ivt, ")");
    nodo.hijo.push_back(tnodo());
    parsinginstruccion(nodo.hijo.back(), vt, ivt);
  } else if (vt[ivt].tipo == "for") {
    nodo = vt[ivt];
    ivt++;
    saltartipo(vt, ivt, "(");
    nodo.hijo = vector<tnodo> (4);
    parsingasignacionsimple(nodo.hijo[0], vt, ivt, ";");
    parsingexpresion(nodo.hijo[1], vt, ivt);
    saltartipo(vt, ivt, ";");
    parsingasignacionsimple(nodo.hijo[2], vt, ivt, ")");
    parsinginstruccion(nodo.hijo[3], vt, ivt);
  } else if (vt[ivt].tipo == "{") {
    parsinglistainstrucciones(nodo, vt, ivt);
  } else if (vt[ivt].tipo == "stop") {
    nodo = vt[ivt];
    ivt++;
    saltartipo(vt, ivt, ";");
  } else if (vt[ivt].tipo == "stopformaterror") {
    nodo = vt[ivt];
    ivt++;
    nodo.hijo = vector<tnodo> (3);
    saltartipo(vt, ivt, "(");
    parsingexpresion(nodo.hijo[0], vt, ivt);
    saltartipo(vt, ivt, ",");
    parsingexpresion(nodo.hijo[1], vt, ivt);
    saltartipo(vt, ivt, ",");
    parsingexpresion(nodo.hijo[2], vt, ivt);
    saltartipo(vt, ivt, ")");
    saltartipo(vt, ivt, ";");
  } else
    seesperabaver(vt, ivt, "{\"if\",\"ident\",\"++\",\"--\",\"{\",\"while\",\"for\",\"foreach\",\"out\",\"stop\"}");
}

void parsinglistainstrucciones(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  nodo.tipo = "lista";
  saltartipo(vt, ivt, "{");
  while (ivt < int(vt.size()) and vt[ivt].tipo != "}") {
    /*
    (vt[ivt].tipo=="if" or vt[ivt].tipo=="identificador" or vt[ivt].tipo=="{"
    or vt[ivt].tipo=="out" or vt[ivt].tipo=="stop" or vt[ivt].tipo=="while" or
    vt[ivt].tipo=="for" or vt[ivt].tipo=="stopformaterror" or vt[ivt].tipo==")) {
    */
    nodo.hijo.push_back(tnodo());
    parsinginstruccion(nodo.hijo.back(), vt, ivt);
  }
  saltartipo(vt, ivt, "}");
}

void parsing(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  if (ivt == int(vt.size()) or vt[ivt].tipo != "main")
    morir("rejected", "The program must have the format \"main { <instructions> }\"",
          "rechazado", "El programa debe tener el formato \"main { <instrucciones> }\"",
          "rebutjat", "El programa ha de tenir el format \"main { <instruccions> }\"");
  nodo = vt[ivt];
  nodo.hijo.push_back(tnodo());
  ivt++;
  if (ivt < int(vt.size()) and vt[ivt].tipo == "(") {
    ivt++;
    if (ivt == int(vt.size()) or vt[ivt].tipo != "identificador")
      seesperabaver(vt, ivt, "\"ident\"");
    nodo.texto = vt[ivt].texto;
    ivt++;
    saltartipo(vt, ivt, ")");
  }
  parsinglistainstrucciones(nodo.hijo[0], vt, ivt);
}

void comprobarnoseusatipo(tnodo const &nodo, string const &tipo,
                          string const &ingles, string const &espanyol, string const &catalan)
{
  if (nodo.tipo == tipo)
    morir("rejected", "Error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": " + ingles,
          "rechazado", "Error linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": " + espanyol,
          "rebutjat", "Error linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": " + catalan);
  for (int i = 0; i < int(nodo.hijo.size()); ++i)
    comprobarnoseusatipo(nodo.hijo[i], tipo, ingles, espanyol, catalan);
}


////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Analisis lexico del string que describe clausulas SAT:

set<string> palabrasclavesat;

set<string> cadenasclavesat;

char listapalabrasclavesat[][80] = {"and", "or", "not", "implies", "iff", "if", "atleast", "atmost", "exactly", ""};

char listacadenasclavesat[][80] = {"(", ")", "-", "|", "&", "<=", "=>", "<=>", ""};

void inicializartokensclavesat()
{
  palabrasclavesat = cadenasclavesat = set<string> ();
  for (int i = 0; string(listapalabrasclavesat[i]) != ""; i++)
    palabrasclavesat.insert(listapalabrasclavesat[i]);
  for (int i = 0; string(listacadenasclavesat[i]) != ""; i++)
    cadenasclavesat.insert(listacadenasclavesat[i]);
}

void leeridentificadorsat(string &s, int &is, vector<ttoken> &vt)
{
  int nextis = is;
  bool dentrodecorchetes = false;
  while (nextis < int(s.size()) and
         ((s[nextis] >= 'a' and s[nextis] <= 'z') or
          (s[nextis] >= 'A' and s[nextis] <= 'Z') or
          (s[nextis] >= '0' and s[nextis] <= '9') or
          s[nextis] == '_' or s[nextis] == '{' or s[nextis] == '}') or
         (dentrodecorchetes and s[nextis] == '-')) {
    if (s[nextis] == '{') dentrodecorchetes = true;
    if (s[nextis] == '}') dentrodecorchetes = false;
    nextis++;
  }
  string id = s.substr(is, nextis - is);
  if (palabrasclavesat.count(id))
    vt.push_back(ttoken(id, "", 0, is + 1));
  else
    vt.push_back(ttoken("identificador", id, 0, is + 1));
  is = nextis;
}

void leertokensat(string &s, int &is, vector<ttoken> &vt)
{
  if ((s[is] >= 'a' and s[is] <= 'z') or (s[is] >= 'A' and s[is] <= 'Z') or (s[is] >= '0' and s[is] <= '9')
      or (s[is] == '_') or (s[is] == '{') or s[is] == '}')
    leeridentificadorsat(s, is, vt);
  else {
    set<string>::iterator it = cadenasclavesat.end();
    do {
      it--;
      string c = *it;
      if (int(s.size()) - is >= int(c.size()) and
          s.substr(is, int(c.size())) == c) {
        vt.push_back(ttoken(c, "", 0, is + 1));
        is += int(c.size());
        return;
      }
    } while (it != cadenasclavesat.begin());
    morir("rejected", "Execution error in lexical analysis of insertsat: \"" + s.substr(0, is) + "\" {ERROR} \"" + s.substr(is) + "\".",
          "rechazado", "Error de ejecucion en el analisis lexico de insertsat: \"" + s.substr(0, is) + "\" {ERROR} \"" + s.substr(is) + "\".",
          "rebutjat", "Error d'execucio en l'analisi lexic de insertsat: \"" + s.substr(0, is) + "\" {ERROR} \"" + s.substr(is) + "\".");
  }
}


void leerentradasat(string &s, vector<ttoken> &vt)
{
  inicializartokensclavesat();
  int is = 0;
  saltarblancos(s, is);
  while (is < int(s.size())) {
    leertokensat(s, is, vt);
    saltarblancos(s, is);
  }
}

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Definicion de tvalor.



ll limiteoverflow = 100000;
ll limitememoria = 1000000;

ll absoluto(ll x)
{
  if (x < 0) return -x;
  return x;
}

void controloverflow(ll val)
{
  if (absoluto(val) >= limiteoverflow)
    morir("rejected", string("Runtime error: the program produces an overflow.\n") +
          "This does not imply that the reduction is wrong, but it is convenient\n" +
          "to find a simpler reduction.",
          "rechazado", string("Error de ejecucion: el programa produce un overflow.\n") +
          "Eso no significa que la reduccion sea erronea, pero si que conviene\n" +
          "buscar una reduccion mas sencilla.",
          "rebutjat", string("Error d'execucio: el programa produeix overflow.") +
          "Aixo no significa que la reduccio sigui erronea, pero si que conve\n" +
          "buscar una reduccio mes senzilla.");

}

int limitesizestring = 20000;

void controllimitesizestring(string &s)
{
  if (int(s.size()) > limitesizestring)
    morir("rejected", string("Runtime error: the program produces a too big string.\n") +
          "This does not imply that the reduction is wrong, but it is convenient\n" +
          "to find a simpler reduction.",
          "rechazado", string("Error de ejecucion: el programa produce un string demasiado grande.\n") +
          "Eso no significa que la reduccion sea erronea, pero si que conviene\n" +
          "buscar una reduccion mas sencilla.",
          "rebutjat", string("Error d'execucio: el programa produeix un string massa gran.") +
          "Aixo no significa que la reduccio sigui erronea, pero si que conve\n" +
          "buscar una reduccio mes senzilla.");
}


struct tvalor {
  int kind; // 0=entero, 1=string, 2=vector de tvalor, 3=referencia a "in", 4=struct
  ll x;
  string s;
  vector<tvalor> v;
  tvalor *ref;
  tnodo *format;
  map<string, tvalor> m;

  tvalor() {
    kind = x = 0;
    format = NULL;
  }
  tvalor(ll inx) {
    kind = 0;
    x = inx;
    controloverflow(inx);
    format = NULL;
  }
  tvalor(string ins) {
    kind = 1;
    s = ins;
    controllimitesizestring(s);
    format = NULL;
  }
  tvalor(int x, const tvalor &h1) {
    kind = 2;
    v.push_back(h1);
    format = NULL;
  }
  tvalor(const tvalor &h1, const tvalor &h2) {
    kind = 2;
    v.push_back(h1);
    v.push_back(h2);
    format = NULL;
  }
  tvalor(const tvalor &h1, const tvalor &h2, const tvalor &h3) {
    kind = 2;
    v.push_back(h1);
    v.push_back(h2);
    v.push_back(h3);
    format = NULL;
  }
};


void valorpordefecto(tnodo &nodo, tvalor &valor)
{
  valor.format = &nodo;
  if (nodo.tipo == "int") {
    valor.kind = 0;
    valor.x = 0;
  } else if (nodo.tipo == "string" or nodo.tipo == "#" or nodo.tipo == "@") {
    valor.kind = 1;
    valor.s = "";
  } else if (nodo.tipo == "struct") {
    valor.kind = 4;
    for (map<string, tnodo>::iterator it = nodo.m.begin(); it != nodo.m.end(); it++)
      valorpordefecto(it->second, valor.m[it->first]);
  } else if (nodo.tipo == "array") {
    valor.kind = 2;
    if (nodo.texto != "") {
      int dimension = stoll(nodo.texto);
      tvalor valoraux;
      valorpordefecto(nodo.hijo[0], valoraux);
      for (int i = 0; i < dimension; i++)
        valor.v.push_back(valoraux);
    }
  } else
    morir("rejected", "Execution error in default value: \"" + nodo.tipo + "\" is not a type.",
          "rechazado", "Error de ejecucion en valor por defecto: \"" + nodo.tipo + "\" no es un tipo.",
          "rebutjat", "Error d'execucio a valor per defecte: \"" + nodo.tipo + "\" no es un tipus.");
}

void construirstruct(string campo1, tvalor &valor1, string campo2, tvalor &valor2,
                     tnodo &nodo, tvalor &valor)
{
  nodo.tipo = "struct";
  nodo.m[campo1] = *valor1.format;
  nodo.m[campo2] = *valor2.format;
  valor.format = &nodo;
  valor.kind = 4;
  valor.m[campo1] = valor1;
  valor.m[campo2] = valor2;
}


////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
// Sacar estadisticas:

#include <sys/time.h>
#include <sys/resource.h>
#include <sstream>
#include <iomanip>
#include <ios>
class timer {
private:
  ll const start;
  static ll get()
  {
    struct rusage usg;
    if (getrusage(RUSAGE_SELF, &usg) == 0)
      return usg.ru_utime.tv_sec * 1000 + usg.ru_utime.tv_usec / 1000;
    return -1;
  }
public:
  timer() : start(get()) {}
  double elapsed() const
  {
    ll current;
    if (start == -1 or (current = get()) == -1)
      return -1;
    return (current - start) / 1000.0;
  }
  string elapsedstring() const
  {
    ostringstream s;
    s << fixed << setprecision(3) << elapsed() << "s";
    return s.str();
  }
};

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
// Uso de minisat:

class sat_solver {
private:
#if defined(USE_MINISAT)
  Minisat::Solver S;
#elif defined(USE_PICOSAT)
  PicoSAT *S;
#endif
  std::map<std::string, int> string_codes;

public:
#if defined(USE_PICOSAT)
  sat_solver()
  {
    S = picosat_init();
  }
  ~sat_solver()
  {
    picosat_reset(S);
  }
#endif
  void add(std::list<std::pair<bool, std::string> > const &clause)
  {
    using namespace std;
    int codeamount = int(string_codes.size());
    for (list<pair<bool, string> >::const_iterator i = clause.begin(); i != clause.end(); ++i)
      if (string_codes.count(i->second) == 0)
        string_codes[i->second] = codeamount++;
#if defined(USE_MINISAT)
    using namespace Minisat;
    while (S.nVars() < codeamount)
      S.newVar();
    vec<Lit> lits;
    for (list<pair<bool, string> >::const_iterator i = clause.begin(); i != clause.end(); ++i)
      if (i->first)
        lits.push( mkLit(string_codes[i->second]));
      else
        lits.push(~mkLit(string_codes[i->second]));
    S.addClause(lits);
#elif defined(USE_PICOSAT)
    for (list<pair<bool, string> >::const_iterator i = clause.begin(); i != clause.end(); ++i)
      if (i->first)
        picosat_add(S, 1 + string_codes[i->second]);
      else
        picosat_add(S, -1 - string_codes[i->second]);
    picosat_add(S, 0);
#endif
  }
  void add(tvalor const &formula)
  {
    for (vector<tvalor>::const_iterator i = formula.v.begin(); i != formula.v.end(); ++i) {
      list<pair<bool, string> > clause;
      for (vector<tvalor>::const_iterator j = i->v.begin(); j != i->v.end(); ++j) {
        string const literal = (j->kind == 0) ? itos(j->x) : j->s;
        if (not literal.empty() and literal[0] == '-')
          clause.push_back(pair<bool, string>(false, literal.substr(1)));
        else
          clause.push_back(pair<bool, string>(true, literal));
      }
      add(clause);
    }
  }
  bool solve()
  {
#if defined(USE_MINISAT)
    using namespace Minisat;
    lbool ret = l_False;
    if (S.simplify()) {
      vec<Lit> assum;
      ret = S.solveLimited(assum);
    }
    return ret == l_True;
#elif defined(USE_PICOSAT)
    int ret = picosat_sat(S, -1);
    return ret == PICOSAT_SATISFIABLE;
#endif
  }
  int numvars() const
  {
    return int(string_codes.size());
  }
  // only call these function if solve() returned true
  bool assignment(std::string const &variable) const
  {
    if (not string_codes.count(variable)) {
      morir("rejected", "Runtime error: accessed the model with an unknown variable name: " + variable + ".",
            "rechazado", "Error de ejecucion: se ha accedido al modelo con un nombre de variable desconocido: " + variable + ".",
            "rebutjat", "Error d'execucio: s'ha accedit al model amb un nom de variable desconegut: " + variable + ".");
    }
#if defined(USE_MINISAT)
    using namespace Minisat;
    return (S.model[string_codes.find(variable)->second] == l_True);
#elif defined(USE_PICOSAT)
    return (picosat_deref(S, 1 + string_codes.find(variable)->second) == 1);
#endif
  }
  bool assignment(int const variable) const
  {
    return assignment(itos(variable));
  }
};

bool compruebasatisfactibilidad(tvalor const &formula,
                                int &vars, int &clauses, double &segresolver)
{
  timer t;
  sat_solver S;
  S.add(formula);
  bool ret = S.solve();
  vars = S.numvars();
  clauses = int(formula.v.size());
  segresolver = t.elapsed();
  return ret;
}


////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Ejecucion de las formulas sat.


vector<string> *historialinsertsat = NULL;
double tiempoinsertsat = 0;
int ejecucionesinsertsat = 0;

int numid = 1;
string generaid()
{
  return "#" + itos(numid++);
}

void subirastring(tvalor &v)
{
  if (v.kind == 1) return;
  v.kind = 1;
  v.s = itos(v.x);
}

string negar(string s)
{
  if (int(s.size()) > 0 and s[0] == '-') return s.substr(1);
  return "-" + s;
}

void errorformulasat(string &s, vector<ttoken> &vt, int &ivt)
{
  int is = int(s.size());
  if (ivt < int(vt.size()))
    is = vt[ivt].columna - 1;
  morir("rejected", "Execution error in syntax analysis of insertsat: \"" + s.substr(0, is) + "\" {ERROR} \"" + s.substr(is) + "\".",
        "rechazado", "Error de ejecucion en el analisis sintactico de insertsat: \"" + s.substr(0, is) + "\" {ERROR} \"" + s.substr(is) + "\".",
        "rebutjat", "Error d'execucio en l'analisi sintactic de insertsat: \"" + s.substr(0, is) + "\" {ERROR} \"" + s.substr(is) + "\".");
}

void errorformulasat(string &s, vector<ttoken> &vt, int &ivt, string mensajeingles, string mensajeespanyol, string mensajecatalan)
{
  int is = int(s.size());
  if (ivt < int(vt.size()))
    is = vt[ivt].columna - 1;
  morir("rejected", "Execution error in syntax analysis of insertsat: \"" + s.substr(0, is) + "\" {ERROR} \"" + s.substr(is) + "\".\n" + mensajeingles,
        "rechazado", "Error de ejecucion en el analisis sintactico de insertsat: \"" + s.substr(0, is) + "\" {ERROR} \"" + s.substr(is) + "\".\n" + mensajeespanyol,
        "rebutjat", "Error d'execucio en l'analisi sintactic de insertsat: \"" + s.substr(0, is) + "\" {ERROR} \"" + s.substr(is) + "\".\n" + mensajecatalan);
}

void saltartiposat(string &s, vector<ttoken> &vt, int &ivt, string tipo)
{
  if (ivt == int(vt.size()) or tipo != vt[ivt].tipo)
    errorformulasat(s, vt, ivt);
  ivt++;
}

string insertarformulasatiff(string &s, tvalor &out, vector<ttoken> &vt, int &ivt);

void generaclausulasladder(const vector<string>& lista, const string& prefijo, tvalor& out) {
  //hacer que la variable "prefijo + i_j" signifique "i de las j primeras variables son ciertas" con 0<=i<=j<=n
  int n = lista.size();
  out.v.push_back(tvalor(0, tvalor(prefijo + "0_0")));
  for (int j = 1; j <= n; ++j) {
    for (int i = 0; i <= j; ++i) {
      string i_j = prefijo + itos(i) + "_" + itos(j);
      string i_j1 = prefijo + itos(i) + "_" + itos(j - 1);
      if (i == 0) {
        out.v.push_back(tvalor(tvalor(negar(i_j)), tvalor(i_j1)));
        out.v.push_back(tvalor(tvalor(negar(i_j)), tvalor(negar(lista[j - 1]))));
        out.v.push_back(tvalor(tvalor(i_j), tvalor(negar(i_j1)), tvalor(lista[j - 1])));
      } else if (i == j) {
        string i1_j1 = prefijo + itos(i - 1) + "_" + itos(j - 1);
        out.v.push_back(tvalor(tvalor(negar(i_j)), tvalor(i1_j1)));
        out.v.push_back(tvalor(tvalor(negar(i_j)), tvalor(lista[j - 1])));
        out.v.push_back(tvalor(tvalor(i_j), tvalor(negar(i1_j1)), tvalor(negar(lista[j - 1]))));
      } else {
        string i1_j1 = prefijo + itos(i - 1) + "_" + itos(j - 1);
        out.v.push_back(tvalor(tvalor(negar(i_j)), tvalor(i1_j1), tvalor(negar(lista[j - 1]))));
        out.v.push_back(tvalor(tvalor(negar(i_j)), tvalor(i_j1), tvalor(lista[j - 1])));
        out.v.push_back(tvalor(tvalor(i_j), tvalor(negar(i1_j1)), tvalor(negar(lista[j - 1]))));
        out.v.push_back(tvalor(tvalor(i_j), tvalor(negar(i_j1)), tvalor(lista[j - 1])));
      }
    }
  }
}

void generaclausulascasokuno(const vector<string>& lista, const string& prefijo, tvalor& out) {
  //variable a_i significa: "almenos una de x_0..x_i es cierta" con 0<=i<n
  //variable b_i significa: "almenos dos de x_0..x_i son ciertas" con 0<=i<n
  int n = lista.size();
  string prefijoa = prefijo + "a";
  string prefijob = prefijo + "b";
  for (int i = 0; i < n - 1; ++i) {
    string a_i = prefijoa + itos(i);
    string a_i1 = prefijoa + itos(i + 1);
    string b_i = prefijob + itos(i);
    string b_i1 = prefijob + itos(i + 1);
    //x_i => a_i
    out.v.push_back(tvalor(tvalor(negar(lista[i])), tvalor(a_i)));
    //a_i => a_i+1
    out.v.push_back(tvalor(tvalor(negar(a_i)), tvalor(a_i1)));
    //b_i => b_i+1
    out.v.push_back(tvalor(tvalor(negar(b_i)), tvalor(b_i1)));
    //a_i and x_i+1 => b_i+1
    out.v.push_back(tvalor(tvalor(negar(a_i)), tvalor(negar(lista[i + 1])), tvalor(b_i1)));
  }
  string a_n1 = prefijoa + itos(n - 1);
  out.v.push_back(tvalor(tvalor(negar(lista[n - 1])), tvalor(a_n1)));
}

string casoalo(const vector<string>& lista, tvalor& out) {
  int n = lista.size();
  string id = generaid();
  tvalor valor;
  valor.kind = 2;
  valor.v.push_back(tvalor(negar(id)));
  for (int i = 0; i < n; i++) {
    out.v.push_back(tvalor(tvalor(id), tvalor(negar(lista[i]))));
    valor.v.push_back(tvalor(lista[i]));
  }
  out.v.push_back(valor);
  return id;
}

void insertarvariablesconvaloresarbitrarios(const vector<string>& lista, tvalor& out) {
  int n = lista.size();
  for (int i = 0; i < n; i++) {
    out.v.push_back(tvalor(tvalor(lista[i]), tvalor(negar(lista[i]))));
  }
}
string ladderencoding(const string &tipo, int k, const vector<string>& lista, tvalor& out) {
  int n = lista.size();
  //casos extremos
  bool siempresat = false;
  if (n == 0 and k == 0) siempresat = true;
  if (tipo == "atleast" and k <= 0) siempresat = true;
  if (tipo == "atmost" and k >= n) siempresat = true;
  if (siempresat) {
    string id = generaid();
    out.v.push_back(tvalor(0, tvalor(id)));
    insertarvariablesconvaloresarbitrarios(lista, out); //para que las variables no "desaparezcan" en
    //los problemas que piden reconstruir la solucion a partir del modelo
    return id;
  }
  bool siempreunsat = false;
  if (tipo != "atmost" and k > n) siempreunsat = true;
  if (tipo != "atleast" and k < 0) siempreunsat = true;
  if (siempreunsat) {
    string id = generaid();
    out.v.push_back(tvalor(0, tvalor(negar(id))));
    insertarvariablesconvaloresarbitrarios(lista, out);
    return id;
  }
  //casos optimizados
  if (k == 1) {
    if (tipo == "atleast") return casoalo(lista, out);
    string prefijo = generaid();
    generaclausulascasokuno(lista, prefijo, out);
    string almenosdos = prefijo + "b" + itos(n - 1);
    if (tipo == "atmost") return negar(almenosdos);
    string almenosuna = casoalo(lista, out);
    string id = generaid();
    out.v.push_back(tvalor(tvalor(negar(id)), tvalor(almenosuna)));
    out.v.push_back(tvalor(tvalor(negar(id)), tvalor(negar(almenosdos))));
    out.v.push_back(tvalor(tvalor(negar(almenosuna)), tvalor(almenosdos), tvalor(id)));
    return id;
  }
  //caso general
  string prefijo = generaid() + "_";
  generaclausulasladder(lista, prefijo, out);
  if (tipo == "exactly") return prefijo + itos(k) + "_" + itos(n);
  string id = generaid();
  tvalor valor(0, tvalor(negar(id)));
  int primero, ultimo;
  if (tipo == "atleast") primero = k, ultimo = n;
  else primero = 0, ultimo = k;
  for (int i = primero; i <= ultimo; ++i) {
    string var = prefijo + itos(i) + "_" + itos(n);
    valor.v.push_back(var);
    out.v.push_back(tvalor(tvalor(negar(var)), tvalor(id)));
  }
  out.v.push_back(valor);
  return id;
}

string insertarformulasatbasica(string &s, tvalor &out, vector<ttoken> &vt, int &ivt)
{
  if (ivt == int(vt.size()))
    errorformulasat(s, vt, ivt);
  if (vt[ivt].tipo == "-" or vt[ivt].tipo == "not") {
    ivt++;
    return negar(insertarformulasatbasica(s, out, vt, ivt));
  } else if (vt[ivt].tipo == "identificador") {
    return vt[ivt++].texto;
  } else if (vt[ivt].tipo == "(") {
    ivt++;
    string sol = insertarformulasatiff(s, out, vt, ivt);
    saltartiposat(s, vt, ivt, ")");
    return sol;
  } else if (vt[ivt].tipo == "atmost" or vt[ivt].tipo == "atleast" or vt[ivt].tipo == "exactly") {
    string tipo = vt[ivt].tipo;
    ivt++;
    bool const tieneparentesis = (ivt < int(vt.size()) and vt[ivt].tipo == "(");
    if (tieneparentesis)
      saltartiposat(s, vt, ivt, "(");
    int k;
    if (ivt < int(vt.size()) and vt[ivt].tipo == "identificador" and esenterosat(vt[ivt].texto)) {
      k = stollsat(vt[ivt].texto);
      ivt++;
    } else
      errorformulasat(s, vt, ivt, "a non-negative integer was expected", "se esperaba un entero no negativo", "s'esperava un enter no negatiu");
    vector<string> lista;
    while (ivt < int(vt.size()) and (not tieneparentesis or vt[ivt].tipo != ")")) {
      lista.push_back(insertarformulasatiff(s, out, vt, ivt));
    }
    if (tieneparentesis)
      saltartiposat(s, vt, ivt, ")");
    //if (int(lista.size())==0)
    //  errorformulasat(s,vt,ivt,"at least one identifier was expected","se esperaba al menos un identificador","s'esperava almenys un identificador");
    return ladderencoding(tipo, k, lista, out);
  } else
    errorformulasat(s, vt, ivt);
  return "";
}

string insertarformulasatand(string &s, tvalor &out, vector<ttoken> &vt, int &ivt)
{
  vector<string> sol;
  sol.push_back(insertarformulasatbasica(s, out, vt, ivt));
  while (ivt < int(vt.size()) and (vt[ivt].tipo == "&" or vt[ivt].tipo == "and")) {
    ivt++;
    sol.push_back(insertarformulasatbasica(s, out, vt, ivt));
  }
  if (int(sol.size()) == 1) return sol[0];
  string id = generaid();
  tvalor valor;
  valor.kind = 2;
  valor.v.push_back(tvalor(id));
  for (int i = 0; i < int(sol.size()); i++) {
    out.v.push_back(tvalor(tvalor(negar(id)), tvalor(sol[i])));
    valor.v.push_back(tvalor(negar(sol[i])));
  }
  out.v.push_back(valor);
  return id;
}

string insertarformulasator(string &s, tvalor &out, vector<ttoken> &vt, int &ivt)
{
  vector<string> sol;
  sol.push_back(insertarformulasatand(s, out, vt, ivt));
  while (ivt < int(vt.size()) and (vt[ivt].tipo == "|" or vt[ivt].tipo == "or")) {
    ivt++;
    sol.push_back(insertarformulasatand(s, out, vt, ivt));
  }
  if (int(sol.size()) == 1) return sol[0];
  string id = generaid();
  tvalor valor;
  valor.kind = 2;
  valor.v.push_back(tvalor(negar(id)));
  for (int i = 0; i < int(sol.size()); i++) {
    out.v.push_back(tvalor(tvalor(id), tvalor(negar(sol[i]))));
    valor.v.push_back(tvalor(sol[i]));
  }
  out.v.push_back(valor);
  return id;
}

string insertarformulasatimplies(string &s, tvalor &out, vector<ttoken> &vt, int &ivt)
{
  string sol1;
  sol1 = insertarformulasator(s, out, vt, ivt);
  if (ivt < int(vt.size()) and (vt[ivt].tipo == "=>" or vt[ivt].tipo == "implies")) {
    ivt++;
    string sol2 = insertarformulasator(s, out, vt, ivt);
    string id = generaid();
    out.v.push_back(tvalor(tvalor(negar(id)), tvalor(negar(sol1)), tvalor(sol2)));
    out.v.push_back(tvalor(tvalor(id), tvalor(sol1)));
    out.v.push_back(tvalor(tvalor(id), tvalor(negar(sol2))));
    return id;
  } else if (ivt < int(vt.size()) and (vt[ivt].tipo == "<=" or vt[ivt].tipo == "if")) {
    ivt++;
    string sol2 = insertarformulasator(s, out, vt, ivt);
    string id = generaid();
    out.v.push_back(tvalor(tvalor(negar(id)), tvalor(sol1), tvalor(negar(sol2))));
    out.v.push_back(tvalor(tvalor(id), tvalor(negar(sol1))));
    out.v.push_back(tvalor(tvalor(id), tvalor(sol2)));
    return id;
  }
  return sol1;
}

string insertarformulasatiff(string &s, tvalor &out, vector<ttoken> &vt, int &ivt)
{
  string sol1;
  sol1 = insertarformulasatimplies(s, out, vt, ivt);
  if (ivt < int(vt.size()) and (vt[ivt].tipo == "<=>" or vt[ivt].tipo == "iff")) {
    ivt++;
    string sol2 = insertarformulasatimplies(s, out, vt, ivt);
    string id = generaid();
    out.v.push_back(tvalor(tvalor(id), tvalor(negar(sol1)), tvalor(negar(sol2))));
    out.v.push_back(tvalor(tvalor(id), tvalor(sol1), tvalor(sol2)));
    out.v.push_back(tvalor(tvalor(negar(id)), tvalor(negar(sol1)), tvalor(sol2)));
    out.v.push_back(tvalor(tvalor(negar(id)), tvalor(sol1), tvalor(negar(sol2))));
    return id;
  }
  return sol1;
}
void insertarformulasat(string &s, tvalor &out, vector<ttoken> &vt)
{
  int ivt = 0;
  string sol = insertarformulasatiff(s, out, vt, ivt);
  if (ivt < int(vt.size()))
    errorformulasat(s, vt, ivt);
  out.v.push_back(tvalor(0, tvalor(sol)));
}

void insertarformulasat(string &s, tvalor &out)
{
  if (historialinsertsat != NULL)
    historialinsertsat->push_back(s);
  timer t;
  vector<ttoken> vt;
  leerentradasat(s, vt);
  insertarformulasat(s, out, vt);
  tiempoinsertsat += t.elapsed();
  ejecucionesinsertsat++;
}

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Ejecucion del programa de entrada:

/*
struct mapping {
  bool calculado;
  set<int> s;
  vector<string> v;
  map<string,int> m;

  mapping()
  {
    calculado=true;
  }
  void insert(tvalor valor)
  {
    calculado=false;
    subirastring(valor);
    //if (valor.kind==0) {
      //s.insert(valor.x);
      //v.push_back(itos(valor.x));
      //m[itos(valor.x)];
    //} else
    if (m.count(valor.s)==0) {
      v.push_back(valor.s);
      m[valor.s];
    }
  }
  tvalor value(tvalor valor,int linea,int columna)
  {
    subirastring(valor);
    //if ((valor.kind==0 and s.count(valor.x)==0) or (valor.kind==1 and m.count(valor.s)==0)) {
    if (m.count(valor.s)==0)
      morir("rejected",string("Internal error line "+itos(linea)+" column "+itos(columna)+": the mapping is accessed with a non-defined value "+valor.s+"."),
      "rechazado",string("Error interno linea "+itos(linea)+" columna "+itos(columna)+": el mapping es accedido con un valor no definido "+valor.s+"."),
      "rebutjat",string("Error intern linea "+itos(linea)+" columna "+itos(columna)+": el mapping es accedit amb un valor no definit "+valor.s+"."));
  //if (valor.kind==0) return valor.x;
    if (calculado==false) {
      int count=1;
      for (int i=0;i<int(v.size());i++) {
  while (s.count(count)) count++;
  m[v[i]]=count++;
      }
      calculado=true;
    }
    return m[valor.s];
  }
};
*/

ll computausomemoria(tvalor &valor)
{
  if (valor.kind == 0) return 0;
  if (valor.kind == 1) return 1; //int(valor.s.size());
  ll suma = int(valor.v.size());
  for (int i = 0; i < int(valor.v.size()); i++)
    suma += computausomemoria(valor.v[i]);
  for (map<string, tvalor>::iterator it = valor.m.begin(); it != valor.m.end(); it++)
    suma += computausomemoria(it->second);
  return suma;
}

void controlmemoria(int memoria)
{
  if (memoria > limitememoria)
    morir("rejected", string("Runtime error: the program uses too much memory.\n") +
          "This does not imply that the reduction is wrong, but it is convenient\n" +
          "to find a simpler reduction.",
          "rechazado", string("Error de ejecucion: el programa usa demasiada memoria.\n") +
          "Eso no significa que la reduccion sea erronea, pero si que conviene\n" +
          "buscar una reduccion mas sencilla.",
          "rebutjat", string("Error d'execucio: el programa utilitza massa memoria.") +
          "Aixo no significa que la reduccio sigui erronea, pero si que conve\n" +
          "buscar una reduccio mes senzilla.");
}

tvalor comprobarentero(string op, tvalor v)
{
  if (v.kind != 0)
    morir("rejected", "Runtime error: '" + op + "' should be applied to integers.",
          "rechazado", "Error de ejecucion: '" + op + "' se debe aplicar a enteros.",
          "rebutjat", "Error d'execucio: '" + op + "' s'ha d'aplicar a enters.");
  return v;
}

void comprobarentero(string op, tvalor v1, tvalor v2)
{
  if (v1.kind != 0 or v2.kind != 0)
    morir("rejected", "Runtime error: '" + op + "' should be applied to integers.",
          "rechazado", "Error de ejecucion: '" + op + "' se debe aplicar a enteros.",
          "rebutjat", "Error d'execucio: '" + op + "' s'ha d'aplicar a enters.");
}

void comprobarstring(string op, tvalor v)
{
  if (v.kind != 1)
    morir("rejected", "Runtime error: '" + op + "' should be applied to strings.",
          "rechazado", "Error de ejecucion: '" + op + "' se debe aplicar a strings.",
          "rebutjat", "Error d'execucio: '" + op + "' s'ha d'aplicar a strings.");
}

void comprobarenteroostring(string op, tvalor v1, tvalor v2)
{
  if ((v1.kind != 0 and v1.kind != 1) or (v2.kind != 0 and v2.kind != 1))
    morir("rejected", "Runtime error: '" + op + "' should be applied to integers or strings.",
          "rechazado", "Error de ejecucion: '" + op + "' se debe aplicar a enteros o strings.",
          "rebutjat", "Error d'execucio: '" + op + "' s'ha d'aplicar a enters o strings.");
}

void comprobarenteroostring(string op, tvalor v)
{
  if (v.kind != 0 and v.kind != 1)
    morir("rejected", "Runtime error: '" + op + "' should be applied to integers or strings.",
          "rechazado", "Error de ejecucion: '" + op + "' se debe aplicar a enteros o strings.",
          "rebutjat", "Error d'execucio: '" + op + "' s'ha d'aplicar a enters o strings.");
}

tvalor operator+(tvalor v1, tvalor v2)
{
  comprobarenteroostring("+", v1, v2);
  if (v1.kind == 0 and v2.kind == 0)
    return v1.x + v2.x;
  subirastring(v1);
  subirastring(v2);
  return v1.s + v2.s;
}

tvalor operator*(tvalor v1, tvalor v2)
{
  comprobarentero("*", v1, v2);
  return v1.x * v2.x;
}

tvalor operator/(tvalor v1, tvalor v2)
{
  comprobarentero("/", v1, v2);
  string op = "/";
  if (v2.x == 0)
    morir("rejected", "Runtime error: '" + op + "' should not have second operand equal to 0.",
          "rechazado", "Error de ejecucion: '" + op + "' no debe tener segundo operando igual a 0.",
          "rebutjat", "Error d'execucio: '" + op + "' no ha de tenir segon operand igual a 0.");
  return v1.x / v2.x;
}

tvalor operator%(tvalor v1, tvalor v2)
{
  comprobarentero("%", v1, v2);
  string op = "%";
  if (v2.x == 0)
    morir("rejected", "Runtime error: '" + op + "' should not have second operand equal to 0.",
          "rechazado", "Error de ejecucion: '" + op + "' no debe tener segundo operando igual a 0.",
          "rebutjat", "Error d'execucio: '" + op + "' no ha de tenir segon operand igual a 0.");
  return v1.x % v2.x;
}

tvalor operator-(tvalor v1, tvalor v2)
{
  comprobarentero("-", v1, v2);
  return v1.x - v2.x;
}

tvalor operator!(tvalor v)
{
  comprobarentero("not", v);
  return not v.x;
}

tvalor operator<(tvalor v1, tvalor v2)
{
  comprobarentero("<", v1, v2);
  return v1.x < v2.x;
}

tvalor operator>(tvalor v1, tvalor v2)
{
  comprobarentero(">", v1, v2);
  return v1.x > v2.x;
}

tvalor operator<=(tvalor v1, tvalor v2)
{
  comprobarentero("<=", v1, v2);
  return v1.x <= v2.x;
}

tvalor operator>=(tvalor v1, tvalor v2)
{
  comprobarentero(">=", v1, v2);
  return v1.x >= v2.x;
}

tvalor operator==(tvalor v1, tvalor v2)
{
  comprobarenteroostring("==", v1, v2);
  if (v1.kind == 0 and v2.kind == 0)
    return v1.x == v2.x;
  subirastring(v1);
  subirastring(v2);
  return v1.s == v2.s;
}

tvalor operator!=(tvalor v1, tvalor v2)
{
  comprobarenteroostring("!=", v1, v2);
  if (v1.kind == 0 and v2.kind == 0)
    return v1.x != v2.x;
  subirastring(v1);
  subirastring(v2);
  return v1.s != v2.s;
}

tvalor max(tvalor v1, tvalor v2)
{
  comprobarentero("max", v1, v2);
  return max(v1.x, v2.x);
}

tvalor min(tvalor v1, tvalor v2)
{
  comprobarentero("min", v1, v2);
  return min(v1.x, v2.x);
}

tvalor abs(tvalor v)
{
  comprobarenteroostring("abs", v);
  if (v.kind == 0) {
    if (v.x < 0) return -v.x;
    return v.x;
  }
  if (int(v.s.size()) > 0 and v.s[0] == '-')
    return v.s.substr(1);
  return v.s;
}

tvalor ejecutaexpresion(tnodo &nodo, tvalor &in, map<string, tvalor> &valor,
                        char const *nombremodelo, sat_solver const *modelo);

tvalor &extraerelemento(tnodo &nodo, tvalor &in, map<string, tvalor> &valor,
                        char const *nombremodelo, sat_solver const *modelo)
{
  if (nodo.tipo == "in") return in;
  if (nodo.tipo == "identificador") {
    if (valor.count(nodo.texto) == 0)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": using the variable \"" + nodo.texto +
            "\" when no value has been assigned to it.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": se utiliza la variable \"" + nodo.texto +
            "\" sin que se le haya asignado ningun valor.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": s'utiliza la variable \"" + nodo.texto +
            "\" sin que se li hagi assignat cap valor.");
    tvalor v = valor[nodo.texto];
    if (v.kind != 3)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": " + nodo.texto + " is not a reference to \"in\" here.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": " + nodo.texto + " no es una referencia a \"in\" aqui.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": " + nodo.texto + " no es una referencia a \"in\" aqui.");
    return *v.ref;
  }
  if (nodo.tipo == "[") {
    tvalor &v1 = extraerelemento(nodo.hijo[0], in, valor, nombremodelo, modelo);
    tvalor v2 = ejecutaexpresion(nodo.hijo[1], in, valor, nombremodelo, modelo);
    if (v1.kind != 2)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": indexed access to a non-array.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso indexado a un no-array.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces indexat a un no-array.");
    comprobarentero("array[...]", v2);
    if (v2.x < 0 or int(v1.v.size()) <= v2.x)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": out of range in array access.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso a array fuera de rango.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces a array fora de rang.");
    return v1.v[v2.x];
  }
  if (nodo.tipo == "back") {
    tvalor &v1 = extraerelemento(nodo.hijo[0], in, valor, nombremodelo, modelo);
    if (v1.kind != 2)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": back access to a non-array.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso back a un no-array.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces back a un no-array.");
    if (int(v1.v.size()) == 0)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": back access to an array with 0 size.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso back a un array de tamanyo 0.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces back a un array de mida 0.");
    return v1.v.back();
  }
  if (nodo.tipo == ".") {
    tvalor &v1 = extraerelemento(nodo.hijo[0], in, valor, nombremodelo, modelo);
    if (v1.kind != 4)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": field access to a non-struct.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso por campo a un no-struct.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces per camp a un no-struct.");
    if (v1.m.count(nodo.texto) == 0)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": the struct does not have a field called " + nodo.texto + ".",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": el struct no tiene un campo llamado " + nodo.texto + ".",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": l'struct no te un camp anomenat " + nodo.texto + ".");
    return v1.m[nodo.texto];
  }
  // Aquest error no s'hauria de donar mai:
  morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": an indexation to \"in\" or \"out\" was expected.",
        "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": se esperaba una indexacion a \"in\" o \"out\".",
        "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": s'esperava una indexacio a \"in\" o \"out\".");
  return in;
}

tvalor ejecutaexpresion(tnodo &nodo, tvalor &in, map<string, tvalor> &valor,
                        char const *nombremodelo, sat_solver const *modelo)
{
  if (nodo.tipo == "identificador") {
    if (valor.count(nodo.texto) == 0)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": using the variable \"" + nodo.texto +
            "\" when no value has been assigned to it.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": se utiliza la variable \"" + nodo.texto +
            "\" sin que se le haya asignado ningun valor.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": s'utiliza la variable \"" + nodo.texto +
            "\" sin que se li hagi assignat cap valor.");
    if (valor[nodo.texto].kind == 3) {
      tvalor &v = *valor[nodo.texto].ref;
      if (v.kind != 0 and v.kind != 1)
        morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": only simple types inside \"in\" can be accessed in an expression.",
              "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": solo se pueden acceder tipos simples dentro de \"in\" en una expresion.",
              "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": nomes es poden accedir tipus simples dins de \"in\" en una expressio.");
      return v;
    }
    return valor[nodo.texto];
  } else if (nodo.tipo == "constante") {
    return stoll(nodo.texto);
  } else if (nodo.tipo == "string") {
    return tvalor(nodo.texto);
  } else if (nodo.tipo == "substr") {
    tvalor s = ejecutaexpresion(nodo.hijo[0], in, valor, nombremodelo, modelo);
    tvalor pos = ejecutaexpresion(nodo.hijo[1], in, valor, nombremodelo, modelo);
    comprobarstring("substr(...,)", s);
    comprobarentero("substr(,...)", pos);
    if (pos.x < 0 or int(s.s.size()) <= pos.x)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": out of range in substring access.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso a substring fuera de rango.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces a substring fora de rang.");
    return s.s.substr(pos.x);
  } else if (nodo.tipo == "size") {
    tvalor &v = extraerelemento(nodo.hijo[0], in, valor, nombremodelo, modelo);
    if (v.kind != 2)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": \"size\" must be applied to an array.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": \"size\" se debe aplicar a un array.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": \"size\" s'ha d'aplicar a un array.");
    return int(v.v.size());
  } else if (nombremodelo != NULL and nodo.tipo == "[" and nodo.hijo[0].tipo == "identificador" and nodo.hijo[0].texto == nombremodelo) {
    tvalor v2 = ejecutaexpresion(nodo.hijo[1], in, valor, nombremodelo, modelo);
    if (v2.kind != 0 and v2.kind != 1)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": the model must be queried with a variable name (i.e., an integer or a string).",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": el modelo debe consultarse con el nombre de una variable (es decir, un entero o un string).",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": el model ha de consultar-se amb el nom d'una variable (es a dir, un enter o un string).");
    tvalor res;
    res.x = (v2.kind == 0) ? modelo->assignment(v2.x) : modelo->assignment(v2.s);
    return res;
  } else if (nodo.tipo == "in" or nodo.tipo == "back" or nodo.tipo == "[" or nodo.tipo == ".") {
    tvalor &v = extraerelemento(nodo, in, valor, nombremodelo, modelo);
    if (v.kind != 0 and v.kind != 1)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": only simple types inside \"in\" can be accessed in an expression.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": solo se pueden acceder tipos simples dentro de \"in\" en una expresion.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": nomes es poden accedir tipus simples dins de \"in\" en una expressio.");
    return v;
  } else if (nodo.tipo == "abs") {
    return abs(ejecutaexpresion(nodo.hijo[0], in, valor, nombremodelo, modelo));
  } else if (nodo.tipo == "and") {
    if (comprobarentero("and", ejecutaexpresion(nodo.hijo[0], in, valor, nombremodelo, modelo)).x == 0) return 0;
    else return comprobarentero("and", ejecutaexpresion(nodo.hijo[1], in, valor, nombremodelo, modelo));
  } else if (nodo.tipo == "or") {
    if (comprobarentero("or", ejecutaexpresion(nodo.hijo[0], in, valor, nombremodelo, modelo)).x == 1) return 1;
    else return comprobarentero("or", ejecutaexpresion(nodo.hijo[1], in, valor, nombremodelo, modelo));
  } else {
    tvalor v[2];
    for (int i = 0; i < int(nodo.hijo.size()); i++)
      v[i] = ejecutaexpresion(nodo.hijo[i], in, valor, nombremodelo, modelo);
    if (nodo.tipo == "-") {
      if (int(nodo.hijo.size()) == 1) return -v[0].x;
      return v[0] - v[1];
    }
    if (nodo.tipo == "max") return max(v[0], v[1]);
    if (nodo.tipo == "min") return min(v[0], v[1]);
    if (nodo.tipo == "+") return v[0] + v[1];
    if (nodo.tipo == "*") return v[0] * v[1];
    if (nodo.tipo == "/") return v[0] / v[1];
    if (nodo.tipo == "%") return v[0] % v[1];
    if (nodo.tipo == "==") return v[0] == v[1];
    if (nodo.tipo == "!=") return v[0] != v[1];
    if (nodo.tipo == "<") return v[0] < v[1];
    if (nodo.tipo == ">") return v[0] > v[1];
    if (nodo.tipo == "<=") return v[0] <= v[1];
    if (nodo.tipo == ">=") return v[0] >= v[1];
    if (nodo.tipo == "not") return !v[0];
  }
  return 0;
}

tvalor &extraerout(tnodo &nodo, tvalor &in, tvalor &out, map<string, tvalor> &valor, int &memoria,
                   char const *nombremodelo, sat_solver const *modelo)
{
  if (nodo.tipo == "out") return out;
  tvalor &v1 = extraerout(nodo.hijo[0], in, out, valor, memoria, nombremodelo, modelo);
  if (nodo.tipo == ".") {
    if (v1.kind != 4)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": field access to a non-struct.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso por campo a un no-struct.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces per camp a un no-struct.");
    if (v1.m.count(nodo.texto) == 0)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": the struct does not have a field called " + nodo.texto + ".",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": el struct no tiene un campo llamado " + nodo.texto + ".",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": l'struct no te un camp anomenat " + nodo.texto + ".");
    return v1.m[nodo.texto];
  }
  if (nodo.tipo == "[") {
    if (v1.kind != 2)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": indexed access to a non-array.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso indexado a un no-array.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces indexat a un no-array.");
    tvalor v2 = ejecutaexpresion(nodo.hijo[1], in, valor, nombremodelo, modelo);
    comprobarentero("array[...]", v2);
    if (v2.x < 0)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": out of range in array access.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso a array fuera de rango.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces a array fora de rang.");
    if (v1.format->texto != "") {
      if (int(v1.v.size()) <= v2.x)
        morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": out of range in array of fixed size access.",
              "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso a array de tamanyo fijo fuera de rango.",
              "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces a array de mida fixa fora de rang.");
      return v1.v[v2.x];
    } else {
      controlmemoria(v2.x + 1);
      if (int(v1.v.size()) <= v2.x) {
        tvalor defecto;
        valorpordefecto(v1.format->hijo[0], defecto);
        int memdefecto = computausomemoria(defecto);
        memoria += (v2.x + 1 - int(v1.v.size())) * (memdefecto + 1);
        controlmemoria(memoria);
        while (int(v1.v.size()) <= v2.x)
          v1.v.push_back(defecto);
      }
      return v1.v[v2.x];
    }
  }
  if (nodo.tipo == "back") {
    if (v1.kind != 2)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": back access to a non-array.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso back a un no-array.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces back a un no-array.");
    if (int(v1.v.size()) == 0)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": back access to an array with 0 size.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acceso back a un array de tamanyo 0.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": acces back a un array de mida 0.");
    return v1.v.back();
  }
  //if (nodo.tipo=="push") {
  if (v1.kind != 2)
    morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": push action on a non-array.",
          "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": accion push sobre un no-array.",
          "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": accio push sobre un no-array.");
  if (v1.format->texto != "")
    morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": push to array of fixed size.",
          "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": push a array de tamanyo fijo.",
          "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": push a array de mida fixa.");
  tvalor defecto;
  valorpordefecto(v1.format->hijo[0], defecto);
  memoria += 1 + computausomemoria(defecto);
  controlmemoria(memoria);
  v1.v.push_back(defecto);
  return v1.v.back();
  //}
}

int digitos(int x)
{
  if (x == 0) return 1;
  int d = 0;
  while (x > 0) {
    d++;
    x /= 10;
  }
  return d;
}

int limitelineamuestratvalor = 200;
int limitenumlineasmuestratvalor = 500;

int generamuestra(tvalor &valor, string &muestra, string prefijo, int &lineas)
{
  if (valor.kind == 4) {
    for (int i = 0; i < int(valor.format->m.size()); i++)
      if (generamuestra(valor.m[valor.format->listacampos()[i]], muestra,
                        prefijo + "." + valor.format->listacampos()[i], lineas))
        return 1;
  } else if (valor.kind == 2) {
    if (valor.format->hijo[0].tipo == "int" or
        valor.format->hijo[0].tipo == "string" or
        valor.format->hijo[0].tipo == "#" or
        valor.format->hijo[0].tipo == "@") {
      string linea = prefijo + "=[";
      for (int i = 0; i < int(valor.v.size()); i++) {
        if (i > 0) linea += " ";
        if (valor.v[i].kind == 0)
          linea += itos(valor.v[i].x);
        else
          linea += valor.v[i].s;
      }
      if (int(linea.size()) > limitelineamuestratvalor)
        linea = linea.substr(0, limitelineamuestratvalor) + " ... ...";
      linea += "]";
      muestra += linea + "\n";
      lineas++;
    } else {
      int d = digitos(max(0, int(valor.v.size()) - 1));
      for (int i = 0; i < int(valor.v.size()); i++)
        if (generamuestra(valor.v[i], muestra, prefijo + "[" + string(d - digitos(i), ' ') + itos(i) + "]", lineas))
          return 1;
    }
  } else {
    string linea = prefijo + "=";
    if (valor.kind == 0)
      linea += itos(valor.x);
    else
      linea += valor.s;
    if (int(linea.size()) > limitelineamuestratvalor)
      linea = linea.substr(0, limitelineamuestratvalor) + " ... ...";
    muestra += linea + "\n";
    lineas++;
  }
  if (lineas > limitenumlineasmuestratvalor) {
    muestra += " ... \n ... \n";
    return 1;
  }
  return 0;
}

void generamuestra(tvalor &valor, string &muestra, string prefijo)
{
  int lineas = 0;
  generamuestra(valor, muestra, prefijo, lineas);
}

void generamuestra(vector<tvalor> &v, vector<string> &muestra, string prefijo)
{
  muestra = vector<string> (int(v.size()), "");
  for (int i = 0; i < int(v.size()); i++) generamuestra(v[i], muestra[i], prefijo);
}

void generamuestra(vector<string> &historialinsertsat, string &muestra, string prefijo)
{
  for (int i = 0; i < int(historialinsertsat.size()) and i < limitenumlineasmuestratvalor; ++i) {
    string linea = prefijo + historialinsertsat[i];
    if (int(linea.size()) > limitelineamuestratvalor)
      linea = linea.substr(0, limitelineamuestratvalor) + " ... ...";
    muestra += linea + "\n";
  }
  if (int(historialinsertsat.size()) > limitenumlineasmuestratvalor)
    muestra += " ... \n ... \n";
}

void generamuestra(vector<vector<string> > &historialesinsertsat, vector<string> &muestra, string prefijo)
{
  muestra = vector<string> (int(historialesinsertsat.size()), "");
  for (int i = 0; i < int(historialesinsertsat.size()); i++)
    generamuestra(historialesinsertsat[i], muestra[i], prefijo);
}
/*
string muestratvalorlinea(tvalor &valor)
{
  if (valor.kind==0) return itos(valor.x);
  if (valor.kind==1) return valor.s;
  if (valor.kind==3) return "REF";
  if (valor.kind!=2) return "{UNKNOWNTYPE}";
  vector<tvalor> &v=valor.v;
  string linea="[";
  for (int i=0;i<int(v.size());i++) {
    if (i>0) linea+=",";
    linea+=muestratvalorlinea(v[i]);
  }
  linea+="]";
  return linea;
}

string muestratvalormuestra(tvalor &valor)
{
  if (valor.kind==0) return "  out="+itos(valor.x);
  if (valor.kind==1) return "  out="+valor.s;
  if (valor.kind==3) return "  out=" "REF";
  if (valor.kind!=2) return "  out=" "{UNKNOWNTYPE}";
  vector<tvalor> &v=valor.v;
  string s="  out=" "[\n";
  {
    int i;
    for (i=0;i<int(v.size()) and i<limitenumlineasmuestratvalor;i++) {
      string linea=muestratvalorlinea(v[i]);
      if (int(linea.size())>limitelineamuestratvalor)
  linea=linea.substr(0,limitelineamuestratvalor)+" ... ... ";
      s+="       "+linea+"\n";
    }
    if (i<int(v.size())) s+="       " "...\n...\n";
  }
  s+="      " "]\n";
  return s;
}
*/
string muestratvalorchivato(tvalor &valor, string prefijo)
{
  string muestra;
  generamuestra(valor, muestra, prefijo);
  return muestra;
}
/*
string muestratvalor(tvalor &valor)
{
  vector<tvalor> &v=valor.v;
  string s;
  for (int i=0;i<int(v.size()) and i<limitenumlineasmuestratvalor;i++) {
    string linea;
    if (v[i].kind==0) linea+=itos(v[i].x)+"\n";
    else if (v[i].kind==1) linea+=v[i].s+"\n";
    else {
      for (int j=0;j<int(v[i].v.size());j++) {
  linea+="   ";
  if (v[i].v[j].kind==0)
    linea+=itos(v[i].v[j].x);
  else
    linea+=v[i].v[j].s;
      }
      s+="\n";
    }
    if (int(linea.size())>limitelineamuestratvalor)
      linea=linea.substr(0,limitelineamuestratvalor)+" ... ... \n";
    s+=linea;
  }
  return s;
}
*/
/*
void muestra2string(tvalor &muestra,string &muestraingles,string &muestraespanyol,string &muestracatalan)
{
  if (muestra.kind!=2)
    morir("rejected","Runtime error: \"muestra\" should be an array.",
    "rechazado","Error de ejecucion: \"muestra\" deberia ser un array.",
    "rebutjat","Error d'execucio: \"muestra\" hauria de ser un array.");
  vector<tvalor> &v=muestra.v;
  for (int i=0;i<int(v.size());i++) {
    if (v[i].kind!=2)
      morir("rejected","Runtime error: \"muestra["+itos(i)+"]\" should be an array.",
      "rechazado","Error de ejecucion: \"muestra["+itos(i)+"]\" deberia ser un array.",
      "rebutjat","Error d'execucio: \"muestra["+itos(i)+"]\" hauria de ser un array.");
    vector<tvalor> &w=v[i].v;
    if (int(w.size())!=3)
      morir("rejected","Runtime error: \"muestra["+itos(i)+"]\" should be an array with 3 elements.",
      "rechazado","Error de ejecucion: \"muestra["+itos(i)+"]\" deberia ser un array con 3 elementos.",
      "rebutjat","Error d'execucio: \"muestra["+itos(i)+"]\" hauria de ser un array amb 3 elements.");
    for (int j=0;j<int(w.size());j++) {
      if (w[j].kind!=0 and w[j].kind!=1)
  morir("rejected","Runtime error: \"muestra["+itos(i)+"]["+itos(j)+"]\" should be integer or string.",
        "rechazado","Error de ejecucion: \"muestra["+itos(i)+"]["+itos(j)+"]\" deberia ser entero o string.",
        "rebutjat","Error d'execucio: \"muestra["+itos(i)+"]["+itos(j)+"]\" hauria de ser enter o string.");
      subirastring(w[j]);
    }
    muestraingles+="  "+w[0].s+"\n";
    muestraespanyol+="  "+w[1].s+"\n";
    muestracatalan+="  "+w[2].s+"\n";
  }
}
*/

void morirtipoinsertsat(tnodo &nodo)
{
  morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": insertsat must be applied to an \"array of array of int_or_string\" where the arrays have non-fixed size, and to a \"string\".",
        "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": insertsat se debe aplicar a un \"array of array of int_or_string\" donde los arrays tienen tamanyo no fijo, y a un \"string\".",
        "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": insertsat s'ha d'aplicar a un \"array of array of int_or_string\" on els arrays tenen mida no fixa, i a un \"string\".");
}

// El resultado de la ejecucion==0 significa que no ha terminado, ==1 que se ha terminado con normalidad.

int infinito = 1000000000;
int finito = 100000;
int tiempoejecucion;

int ejecuta(tnodo &nodo, tvalor &in, tvalor &out, map<string, tvalor> &valor, int &memoria,
            char const *nombremodelo, sat_solver const *modelo)
{
  tiempoejecucion--;
  if (tiempoejecucion < 0)
    morir("rejected", "Runtime error: the execution time of the reduction is too big.",
          "rechazado", "Error de ejecucion: el tiempo de ejecucion de la reduccion es excesivo.",
          "rebutjat", "Error d'execucio: el temps d'execucio de la reduccio es execessiu.");
  if (nodo.tipo == ";") {
  } else if (nodo.tipo == "insertsat") {
    tvalor &v1 = ((int(nodo.hijo.size()) == 2) ? (extraerout(nodo.hijo[0], in, out, valor, memoria, nombremodelo, modelo)) : out);
    tvalor v2 = ejecutaexpresion(nodo.hijo.back(), in, valor, nombremodelo, modelo);
    if (v1.format->tipo != "array" or v1.format->texto != "" or v1.format->hijo[0].tipo != "array"
        or v1.format->hijo[0].texto != "" or
        (v1.format->hijo[0].hijo[0].tipo != "string" and v1.format->hijo[0].hijo[0].tipo != "#" and v1.format->hijo[0].hijo[0].tipo != "@")
        or (v2.kind != 0 and v2.kind != 1))
      morirtipoinsertsat(nodo);
    int lenout = int(v1.v.size());
    subirastring(v2);
    insertarformulasat(v2.s, v1);
    tnodo* formatarray = &(v1.format->hijo[0]);
    tnodo* formatstring = &(v1.format->hijo[0].hijo[0]);
    for (int i = lenout; i < int(v1.v.size()); i++) {
      memoria += 1 + computausomemoria(v1.v[i]);
      tvalor &valoraux = v1.v[i];
      valoraux.format = formatarray;
      for (int j = 0; j < int(valoraux.v.size()); j++)
        valoraux.v[j].format = formatstring;
    }
    controlmemoria(memoria);
  } else if (nodo.tipo == "push") {
    extraerout(nodo, in, out, valor, memoria, nombremodelo, modelo);
  } else if (nodo.tipo == "if") {
    tvalor r = ejecutaexpresion(nodo.hijo[0], in, valor, nombremodelo, modelo);
    comprobarentero("if (...)", r);
    if (r.x) {
      int e = ejecuta(nodo.hijo[1], in, out, valor, memoria, nombremodelo, modelo);
      if (e) return e;
    } else if (int(nodo.hijo.size()) == 3) {
      int e = ejecuta(nodo.hijo[2], in, out, valor, memoria, nombremodelo, modelo);
      if (e) return e;
    }
  } else if (nodo.tipo == "while") {
    for (;;) {
      tvalor r = ejecutaexpresion(nodo.hijo[0], in, valor, nombremodelo, modelo);
      comprobarentero("while (...)", r);
      if (not r.x) break;
      int e = ejecuta(nodo.hijo[1], in, out, valor, memoria, nombremodelo, modelo);
      if (e) return e;
    }
  } else if (nodo.tipo == "foreach") {
    int indicereferencia = (nodo.hijo.size() == 3 ? 0 : 1);
    if (nombremodelo != NULL and (nodo.hijo[0].texto == nombremodelo or (indicereferencia and nodo.hijo[indicereferencia].texto == nombremodelo)))
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": foreach(...;) cannot overwrite the model variable \"" + nombremodelo + "\".",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": foreach(...;) no puede sobreescribir la variable \"" + nombremodelo + "\" que contiene el modelo.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": foreach(...;) no pot sobreescriure la variable \"" + nombremodelo + "\" que conte el model.");
    tvalor &v2 = extraerelemento(nodo.hijo[indicereferencia + 1], in, valor, nombremodelo, modelo);
    if (v2.kind != 2)
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": foreach(;...) requires a reference to \"in\" being an array.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": foreach(;...) requiere de una referencia a \"in\" que sea un array.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": foreach(;...) necessita una referencia a \"in\" que sigui un array.");
    for (int i = 0; i < int(v2.v.size()); i++) {
      if (indicereferencia) {
        valor[nodo.hijo[0].texto].kind = 0;
        valor[nodo.hijo[0].texto].x = i;
      }
      valor[nodo.hijo[indicereferencia + 0].texto].kind = 3;
      valor[nodo.hijo[indicereferencia + 0].texto].ref = &v2.v[i];
      int e = ejecuta(nodo.hijo[indicereferencia + 2], in, out, valor, memoria, nombremodelo, modelo);
      if (e) return e;
    }
  } else if (nodo.tipo == "for") {
    int e = ejecuta(nodo.hijo[0], in, out, valor, memoria, nombremodelo, modelo);
    if (e) return e;
    for (;;) {
      tvalor r = ejecutaexpresion(nodo.hijo[1], in, valor, nombremodelo, modelo);
      comprobarentero("for (;...;)", r);
      if (not r.x) break;
      int e;
      e = ejecuta(nodo.hijo[3], in, out, valor, memoria, nombremodelo, modelo);
      if (e) return e;
      e = ejecuta(nodo.hijo[2], in, out, valor, memoria, nombremodelo, modelo);
      if (e) return e;
    }
  } else if (nodo.tipo == "++") {
    tvalor valorid = ejecutaexpresion(nodo.hijo[0], in, valor, nombremodelo, modelo);
    comprobarentero("++", valorid);
    valor[nodo.hijo[0].texto].x++;
  } else if (nodo.tipo == "--") {
    tvalor valorid = ejecutaexpresion(nodo.hijo[0], in, valor, nombremodelo, modelo);
    comprobarentero("--", valorid);
    valor[nodo.hijo[0].texto].x--;
  } else if (nodo.tipo == "=") {
    if (nombremodelo != NULL and (nodo.hijo[0].texto == nombremodelo))
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": cannot overwrite the model variable \"" + nombremodelo + "\".",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": no se puede sobreescribir la variable \"" + nombremodelo + "\" que contiene el modelo.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": no es pot sobreescriure la variable \"" + nombremodelo + "\" que conte el model.");
    tvalor v2 = ejecutaexpresion(nodo.hijo[1], in, valor, nombremodelo, modelo);
    //if (nodo.hijo[0].tipo=="identificador")
    // Haria falta aqui comprobar que lo que se asigna es de tipo entero o string?
    valor[nodo.hijo[0].texto] = v2;
  } else if (nodo.tipo == "&=") {
    if (nombremodelo != NULL and (nodo.hijo[0].texto == nombremodelo))
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": cannot overwrite the model variable \"" + nombremodelo + "\".",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": no se puede sobreescribir la variable \"" + nombremodelo + "\" que contiene el modelo.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": no es pot sobreescriure la variable \"" + nombremodelo + "\" que conte el model.");
    tvalor &v2 = extraerelemento(nodo.hijo[1], in, valor, nombremodelo, modelo);
    valor[nodo.hijo[0].texto].kind = 3;
    valor[nodo.hijo[0].texto].ref = &v2;
  } else if (nodo.tipo == "=,") {
    tvalor &v1 = extraerout(nodo.hijo[0], in, out, valor, memoria, nombremodelo, modelo);
    memoria -= computausomemoria(v1);

    if (int(nodo.hijo.size()) == 2) {
      tvalor v2 = ejecutaexpresion(nodo.hijo[1], in, valor, nombremodelo, modelo);
      // Haria falta aqui comprobar que lo que se asigna es de tipo entero o string?
      if (v1.format->tipo == "int") {
        if (v2.kind != 0)
          morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": incompatible types in assignment.\nAn \"int\" was expected.",
                "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipos incompatibles en la asignacion.\nSe esperaba un \"int\".",
                "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipus incompatibles en l'assignacio.\nS'esperava un \"int\".");
        // No se copia v1=v2 para mantener "tnodo *format;" de v1.
        v1.kind = v2.kind;
        v1.x = v2.x;
        v1.s = v2.s;
      } else if (v1.format->tipo == "string" or v1.format->tipo == "#" or v1.format->tipo == "@") {
        // Este error creo que no deberia tener lugar nunca porque el ejecuta expresion siempre da int o string.
        if (v2.kind != 0 and v2.kind != 1)
          morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": incompatible types in assignment.\nAn \"int\" or \"string\" was expected.",
                "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipos incompatibles en la asignacion.\nSe esperaba un \"int\" o \"string\".",
                "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipus incompatibles en l'assignacio.\nS'esperava un \"int\" o \"string\".");
        // No se copia v1=v2 para mantener "tnodo *format;" de v1.
        v1.kind = v2.kind;
        v1.x = v2.x;
        v1.s = v2.s;
      } else
        morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": incompatible types in assignment.\nOnly simple types can be assigned.",
              "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipos incompatibles en la asignacion.\nSolo se pueden asignar tipos simples.",
              "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipus incompatibles en l'assignacio.\nNomes es poden assignar tipus simples.");
    } else if (v1.kind == 2) {
      if (v1.format->hijo[0].tipo != "int" and v1.format->hijo[0].tipo != "string" and
          v1.format->hijo[0].tipo != "#" and v1.format->hijo[0].tipo != "@")
        morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": Only simple types can be assigned,\nand the positions of the array do not have simple types.",
              "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": Solo se pueden asignar tipos simples,\ny las posiciones del array no tienen tipos simples.",
              "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": Nomes es poden assignar tipus simples,\ni les posicions de l'array no tenen tipus simples.");
      if (v1.format->texto != "") {
        int tamanyo = stoll(v1.format->texto);
        if (tamanyo != int(nodo.hijo.size()) - 1)
          morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": The number of expressions does not coincide with the fixed size of the array.",
                "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": el numero de expresiones no coincide con el tamanyo fijo del array.",
                "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": el nombre d'expressions no coincideix amb la mida fixa de l'array.");
      } else {
        tvalor defecto;
        valorpordefecto(v1.format->hijo[0], defecto);
        v1.v = vector<tvalor> (int(nodo.hijo.size()) - 1, defecto);
      }
      for (int i = 1; i < int(nodo.hijo.size()); i++) {
        tvalor v2 = ejecutaexpresion(nodo.hijo[i], in, valor, nombremodelo, modelo);
        if (v1.format->hijo[0].tipo == "int" and v2.kind != 0)
          morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": incompatible types in assignment.\nAn \"int\" was expected in the expresion number " + itos(i) + ".",
                "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipos incompatibles en la asignacion.\nSe esperaba un \"int\" en la expresion numero " + itos(i) + ".",
                "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipus incompatibles en l'assignacio.\nS'esperava un \"int\" a l'expressio numero " + itos(i) + ".");
        v1.v[i - 1].kind = v2.kind;
        v1.v[i - 1].x = v2.x;
        v1.v[i - 1].s = v2.s;
      }
    } else if (v1.kind == 4) {
      if (int(nodo.hijo.size()) - 1 != int(v1.format->m.size()))
        morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": the number of expressions does not coincide with the number of fields in the struct.",
              "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": el numero de expresiones no coincide con el numero de campos del struct.",
              "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": el nombre d'expressions no coincideix amb el nombre de camps de l'struct.");
      for (int i = 1; i < int(nodo.hijo.size()); i++) {
        tvalor v2 = ejecutaexpresion(nodo.hijo[i], in, valor, nombremodelo, modelo);
        if (v1.format->m[v1.format->listacampos()[i - 1]].tipo == "int" and v2.kind != 0)
          morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": incompatible types in assignment.\nAn \"int\" was expected in the expresion number " + itos(i) + ".",
                "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipos incompatibles en la asignacion.\nSe esperaba un \"int\" en la expresion numero " + itos(i) + ".",
                "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipus incompatibles en l'assignacio.\nS'esperava un \"int\" a l'expressio numero " + itos(i) + ".");
        if (v1.format->m[v1.format->listacampos()[i - 1]].tipo != "int" and
            v1.format->m[v1.format->listacampos()[i - 1]].tipo != "string" and
            v1.format->m[v1.format->listacampos()[i - 1]].tipo != "#" and
            v1.format->m[v1.format->listacampos()[i - 1]].tipo != "@")
          morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": incompatible types in assignment.\nThe field number " + itos(i) + " of the struct is not \"int\" or \"string\".",
                "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipos incompatibles en la asignacion.\nEl campo numero " + itos(i) + " del struct no es \"int\" o \"string\".",
                "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipus incompatibles en l'assignacio.\nEl camp numero " + itos(i) + " del struct no es \"int\" o \"string\".");
        v1.m[v1.format->listacampos()[i - 1]].kind = v2.kind;
        v1.m[v1.format->listacampos()[i - 1]].x = v2.x;
        v1.m[v1.format->listacampos()[i - 1]].s = v2.s;
      }
    } else
      morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": incompatible types in assignment.\nOnly simple types can be assigned.",
            "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipos incompatibles en la asignacion.\nSolo se pueden asignar tipos simples.",
            "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": tipus incompatibles en l'assignacio.\nNomes es poden assignar tipus simples.");
    memoria += computausomemoria(v1);
    controlmemoria(memoria);
  } else if (nodo.tipo == "stop") {
    return 1;
    /*
    } else if (nodo.tipo=="stopformaterror") {
    tvalor h0=ejecutaexpresion(nodo.hijo[0],in,valor);
    comprobarstring("stopformaterror(...,,)",h0);
    tvalor h1=ejecutaexpresion(nodo.hijo[1],in,valor);
    comprobarstring("stopformaterror(,...,)",h1);
    tvalor h2=ejecutaexpresion(nodo.hijo[2],in,valor);
    comprobarstring("stopformaterror(,,...)",h2);
    string muestraingles,muestraespanyol,muestracatalan;
    muestra2string(muestra,muestraingles,muestraespanyol,muestracatalan);
    string muestraout=muestratvalormuestra(in);
    morirpuro(
        "rejected","Format error in the output produced by your program: "+h0.s+".\n\nThe input of your program is:\n\n"+muestraingles+"\nThe output of your program is:\n\n"+muestraout,
        "rechazado","Error de formato en la salida producida por tu programa: "+h1.s+".\n\nLa entrada de tu programa es:\n\n"+muestraespanyol+"\nLa salida de tu programa es:\n\n"+muestraout,
        "rebutjat","Error de format en la sortida produida pel teu programa: "+h2.s+".\n\nLa entrada del teu programa es:\n\n"+muestracatalan+"\nLa sortida del teu programa es:\n\n"+muestraout);

    } else if (nodo.tipo=="mapping") {
    m.insert(ejecutaexpresion(nodo.hijo[0],in,valor));
    */
  } else if (nodo.tipo == "lista") {
    for (int i = 0; i < int(nodo.hijo.size()); i++)
      if (ejecuta(nodo.hijo[i], in, out, valor, memoria, nombremodelo, modelo))
        return 1;
  } else
    morir("rejected", "Runtime error line " + itos(nodo.linea) + " column " + itos(nodo.columna) + ": unknown instruction \"" + nodo.tipo + "\".",
          "rechazado", "Error de ejecucion linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": instruccion desconocida \"" + nodo.tipo + "\".",
          "rebutjat", "Error d'execucio linea " + itos(nodo.linea) + " columna " + itos(nodo.columna) + ": instruccio desconeguda \"" + nodo.tipo + "\".");
  return 0;
}

void ejecuta(tnodo &nodo, tvalor &in, tvalor &out,
             char const *nombremodelo = NULL, sat_solver const *modelo = NULL)
{
  numid = 1;
  map<string, tvalor> valor;
  int memoria = computausomemoria(out);

  ejecuta(nodo.hijo[0], in, out, valor, memoria, nombremodelo, modelo);
}

void ejecuta(tnodo &nodo, vector<tvalor> &vin, vector<tvalor> &vout, tnodo &formatout,
             string internalerroringles, string internalerrorespanyol, string internalerrorcatalan,
             int tiempoejecucionini,
             vector<vector<string> > *historialesinsertsat = NULL)
{
  prefijoerroringles = internalerroringles;
  prefijoerrorespanyol = internalerrorespanyol;
  prefijoerrorcatalan = internalerrorcatalan;
  tvalor defecto;
  valorpordefecto(formatout, defecto);
  vout = vector<tvalor> (int(vin.size()), defecto);
  if (historialesinsertsat != NULL) {
    *historialesinsertsat = vector<vector<string> >(int(vin.size()), vector<string>());
    tiempoinsertsat = 0;
    ejecucionesinsertsat = 0;
  }
  for (int i = 0; i < int(vin.size()); i++) {
    if (historialesinsertsat != NULL)
      historialinsertsat = &(*historialesinsertsat)[i];
    tiempoejecucion = tiempoejecucionini;
    ejecuta(nodo, vin[i], vout[i]);
  }
  if (historialesinsertsat != NULL)
    historialinsertsat = NULL;
}

void ejecutareconstruccion(tnodo &reconstructor, tvalor &in, tnodo &formatout, sat_solver const *modelo, string &muestrasolucion,
                           string &ficherovalidador, tnodo &validador, tnodo &formatvalidador, tvalor &validado)
{
  prefijoerroringles = prefijoerrorespanyol = prefijoerrorcatalan = "";
  tvalor out;
  valorpordefecto(formatout, out);
  tiempoejecucion = infinito;
  ejecuta(reconstructor, in, out, "model", modelo);
  generamuestra(out, muestrasolucion, "  out");
  prefijoerroringles = "Internal error running validator: " + ficherovalidador + "\n";
  prefijoerrorespanyol = "Error interno ejecutando validator: " + ficherovalidador + "\n";
  prefijoerrorcatalan = "Error intern executant validator: " + ficherovalidador + "\n";
  tvalor jpysolucion;
  tnodo nodojpysolucion;
  construirstruct("input", in, "solution", out, nodojpysolucion, jpysolucion);
  valorpordefecto(formatvalidador, validado);
  tiempoejecucion = infinito;
  ejecuta(validador, jpysolucion, validado);
  prefijoerroringles = prefijoerrorespanyol = prefijoerrorcatalan = "";
}


////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Errores genericos:

void errorprogramademasiadogrande()
{
  morir("rejected", "Error: the program is too big. Please, find a simpler solution",
        "rechazado", "Error: el programa es innecesariamente largo. Busca una solucion mas sencilla",
        "rebutjat", "Error: el programa es innecesariament llarg. Busca una solucio mes senzilla");
}

void errorcosasdespuesdelprograma(int linea, int columna)
{
  morir("rejected", "Error line " + itos(linea) + " column " + itos(columna) +
        ": there should not be anything else just after the program.",
        "rechazado", "Error linea " + itos(linea) + " columna " + itos(columna) +
        ": no deberia haber nada mas tras la ultima llave del programa.",
        "rebutjat", "Error linea " + itos(linea) + " columna " + itos(columna) +
        ": no hi hauria d'haver res mes despres de l'ultima clau del programa.");
}

void errorrespuesta(string ingles, string espanyol, string catalan, string &in, string &out)
{
  morir("rejected",
        "Error: the " + ingles + " answer is not preserved when your reduction\n" +
        "receives the following input:\n\n" + in + "\nThe corresponding obtained output is:\n\n" + out +
        "\nIf you consider that the judge verdict is not correct,\n" +
        "try to submit a simpler reduction in order to ease the testing process.",
        "rechazado",
        "Error: no se preserva la respuesta " + espanyol + " cuando tu reduccion\n" +
        "recibe la siguiente entrada:\n\n" + in + "\nLa correspondiente salida obtenida es:\n\n" + out +
        "\nSi consideras que el veredicto del juez no es correcto,\n" +
        "trata de enviar una reduccion mas sencilla para facilitar la comprobacion.",
        "rebutjat",
        "Error: no es preserva la resposta " + catalan + " quan la teva reduccio\n" +
        "rep la seguent entrada:\n\n" + in + "\nLa corresponent sortida obtinguda es:\n\n" + out +
        "\nSi consideres que el veredicte del jutge no es correcte,\n" +
        "mira d'enviar una reduccio mes senzilla a fi de facilitar la seva comprovacio.");
}

void errorrespuesta2SAT(string ingles, string espanyol, string catalan, string &in, string &out,
                        string muestrasolucion = "", string muestraingles = "", string muestraespanyol = "", string muestracatalan = "")
{
  bool mostrarmuestra = not muestrasolucion.empty() or not muestraingles.empty()
                        or not muestraespanyol.empty() or not muestracatalan.empty();
  morir("rejected",
        "Error: the " + ingles + " answer is not preserved when your reduction to SAT\n" +
        "receives the following input:\n\n" + in + "\nThe corresponding generated formula is:\n\n" + out +
        (mostrarmuestra ? "\nThe corresponding reconstructed solution is:\n\n" + muestrasolucion + "\n" + muestraingles + "\n" : string()) +
        "\nIf you consider that the judge verdict is not correct,\n" +
        "try to submit a simpler reduction in order to ease the testing process.",
        "rechazado",
        "Error: no se preserva la respuesta " + espanyol + " cuando tu reduccion a SAT\n" +
        "recibe la siguiente entrada:\n\n" + in + "\nLa correspondiente formula generada es:\n\n" + out +
        (mostrarmuestra ? "\nLa correspondiente solucion reconstruida es\n\n" + muestrasolucion + "\n" + muestraespanyol + "\n" : string()) +
        "\nSi consideras que el veredicto del juez no es correcto,\n" +
        "trata de enviar una reduccion mas sencilla para facilitar la comprobacion.",
        "rebutjat",
        "Error: no es preserva la resposta " + catalan + " quan la teva reduccio a SAT\n" +
        "rep la seguent entrada:\n\n" + in + "\nLa corresponent formula generada es:\n\n" + out +
        (mostrarmuestra ? "\nLa corresponent solucio reconstruida es:\n\n" + muestrasolucion + "\n" + muestracatalan + "\n" : string()) +
        "\nSi consideres que el veredicte del jutge no es correcte,\n" +
        "mira d'enviar una reduccio mes senzilla a fi de facilitar la seva comprovacio.");
}

void errorreconstruccion(string ingles, string espanyol, string catalan, string &in, string &out)
{
  morir("rejected",
        "Error: the reduction is apparently correct, but the reconstructed solution is\n"
        "wrong when your programs receive the following input:\n\n" + in + "\nThe corresponding reconstructed solution is:\n\n" + out +
        (not ingles.empty() ? "\n" + ingles + "\n" : string()),
        "rechazado",
        "Error: la reduccion es aparentemente correcta, pero la reconstruccion de la solucion\n"
        "esta mal cuando tus programas reciben la siguiente entrada:\n\n" + in + "\nLa correspondiente solucion reconstruida es:\n\n" + out +
        (not espanyol.empty() ? "\n" + espanyol + "\n" : string()),
        "rebutjat",
        "Error: la reduccio es aparentment correcta, pero la reconstruccio de la solucio\n"
        "esta malament quan els teus programes reben la seguent entrada:\n\n" + in + "\nLa corresponent solucio reconstruida es:\n\n" + out +
        (not catalan.empty() ? "\n" + catalan + "\n" : string()));
}

void mensajeaceptacion()
{
  morir("accepted", "Reduction apparently correct.",
        "aceptado", "Reduccion aparentemente correcta.",
        "acceptat", "Reduccio aparentment correcta.");
}

void mensajeaceptacionconreconstruccion()
{
  morir("accepted", "Reduction and solution reconstruction apparently correct.",
        "aceptado", "Reduccion y reconstruccion de solucion aparentemente correctos.",
        "acceptat", "Reduccio i reconstruccio de solucio aparentment correctes.");
}


////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Analisis lexico del formateador (analizador de tipo):

set<string> palabrasclaveformat = {"struct", "array", "int", "string", "index", "of"};
set<string> cadenasclaveformat = {"{", "}", "[", "]", ":", "//"};

void leeridentificadorformat(string &s, int &is, vector<ttoken> &vt, int linea)
{
  int nextis = is;
  while (nextis < int(s.size()) and
         (esletra(s[nextis]) or esnumero(s[nextis]) or s[nextis] == '_'))
    nextis++;
  string id = s.substr(is, nextis - is);
  if (palabrasclaveformat.count(id))
    vt.push_back(ttoken(id, "", linea, is + 1));
  else
    vt.push_back(ttoken("identificador", id, linea, is + 1));
  is = nextis;
}

void leerconstanteformat(string &s, int &is, vector<ttoken> &vt, int linea)
{
  int nextis = is;
  while (nextis<int(s.size()) and s[nextis] >= '0' and s[nextis] <= '9') nextis++;
  vt.push_back(ttoken("constante", s.substr(is, nextis - is), linea, is + 1));
  is = nextis;
}

void leertokenformat(string &s, int &is, vector<ttoken> &vt, int linea)
{
  if (esletra(s[is]) or (s[is] == '_')) {
    leeridentificadorformat(s, is, vt, linea);
    return;
  }
  else if (esnumero(s[is])) {
    leerconstanteformat(s, is, vt, linea);
    return;
  }
  else {
    for (string c : cadenasclaveformat) {
      if (int(s.size()) >= is + int(c.size()) and s.substr(is, int(c.size())) == c) {
        if (c == "//") {
          is = int(s.size());
        }
        else {
          vt.push_back(ttoken(c, "", linea, is + 1));
          is += int(c.size());
        }
        return;
      }
    }
  }
  rechazar(linea, is + 1, "there is no correspondence for \"" + s.substr(is) + "\"");
}

void leerentradaformat(string &s, vector<ttoken> &vt, int linea)
{
  int is = 0;
  saltarblancos(s, is);
  while (is < int(s.size())) {
    leertokenformat(s, is, vt, linea);
    saltarblancos(s, is);
  }
}

void leerentradaformat(vector<string> &vs, vector<ttoken> &vt)
{
  for (int i = 0; i < int(vs.size()); i++)
    leerentradaformat(vs[i], vt, i + 1);
}

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Analisis sintactico del formateador:

void parsingformat(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  if (ivt == int(vt.size()))
    seesperabaver(vt, ivt, "{\"struct\",\"array\",\"string\",\"int\"}");
  if (vt[ivt].tipo == "struct") {
    nodo = vt[ivt];
    ivt++;
    saltartipo(vt, ivt, "{");
    while (ivt < int(vt.size()) and vt[ivt].tipo == "identificador") {
      string ident = vt[ivt].texto;
      if (nodo.m.count(ident))
        rechazar(vt[ivt].linea, vt[ivt].columna,
              "the field \"" + ident + "\" has been defined twice in the struct.");
      ivt++;
      saltartipo(vt, ivt, ":");
      parsingformat(nodo.m[ident], vt, ivt);
    }
    saltartipo(vt, ivt, "}");
  } else if (vt[ivt].tipo == "int" or vt[ivt].tipo == "string") {
    nodo = vt[ivt];
    ivt++;
  } else if (vt[ivt].tipo == "array") {
    nodo = vt[ivt];
    nodo.hijo.push_back(tnodo());
    ivt++;
    if (ivt < int(vt.size()) and vt[ivt].tipo == "[") {
      ivt++;
      if (ivt == int(vt.size()) or vt[ivt].tipo != "constante")
        seesperabaver(vt, ivt, "\"constante\"");
      nodo.texto = vt[ivt].texto;
      ivt++;
      saltartipo(vt, ivt, "]");
    }
    saltartipo(vt, ivt, "of");
    parsingformat(nodo.hijo[0], vt, ivt);
  } else
    seesperabaver(vt, ivt, "{\"struct\",\"array\",\"string\",\"int\"}");
}

int limitenumtokens = 5000;

void leerformatstring(string stringformat, tnodo &nodoformat)
{
  prefijoerroringles = "Internal error reading format: " + stringformat + "\n";
  vector<string> vs(1, stringformat);
  vector<ttoken> vt;
  leerentradaformat(vs, vt);
  if (int(vt.size()) > limitenumtokens)
    errorprogramademasiadogrande();
  int ivt = 0;
  parsingformat(nodoformat, vt, ivt);
  if (ivt < int(vt.size()))
    errorcosasdespuesdelprograma(vt[ivt].linea, vt[ivt].columna);
}

void leerformatsfichero(string ficheroformat, tnodo &nodoformat1, tnodo &nodoformat2)
{
  prefijoerroringles = "Internal error reading format: " + ficheroformat + "\n";
  vector<string> vs = leerfichero(ficheroformat);
  vector<ttoken> vt;
  leerentradaformat(vs, vt);
  if (int(vt.size()) > limitenumtokens)
    errorprogramademasiadogrande();
  int ivt = 0;
  parsingformat(nodoformat1, vt, ivt);
  parsingformat(nodoformat2, vt, ivt);
  if (ivt < int(vt.size()))
    errorcosasdespuesdelprograma(vt[ivt].linea, vt[ivt].columna);
}

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////

string eliminaespaciosycomentarios(string s)
{
  string nexts;
  for (int i = 0; i < int(s.size()); i++) {
    if (i + 1 < int(s.size()) and s[i] == '/' and s[i + 1] == '/')
      break;
    if (s[i] != ' ' and s[i] != '\t')
      nexts.push_back(s[i]);
  }
  return nexts;
}

void separarjps(vector<string> &vs, vector<vector<string> > &vvs)
{
  bool nuevojp = true;
  for (string linea : vs) {
    string contenido = eliminaespaciosycomentarios(linea);
    if (contenido == "----")
      nuevojp = true;
    else if (contenido != "") {
      if (nuevojp) vvs.push_back(vector<string> ());
      nuevojp = false;
      vvs.back().push_back(linea);
    }
  }
}

void leerlineajp(string &s, tvalor &valor, tnodo &format)
{
  if (eliminaespaciosycomentarios(s) == "") return;
  tvalor lista;
  lista.kind = 2;
  lista.format = &format;
  istringstream ci(s);
  int x;
  while (ci >> x) {
    lista.v.push_back(x);
    lista.v.back().format = &(format.hijo[0]);
  }
  valor.v.push_back(lista);
}

void leerjp(vector<string> &vs, tvalor &valor, tnodo &format)
{
  valor.kind = 2;
  valor.format = &format;
  for (string linea : vs)
    leerlineajp(linea, valor, format.hijo[0]);
}

void leerjps(string ficherojp, vector<tvalor> &v, tnodo &format)
{
  vector<string> vs = leerfichero(ficherojp);
  vector<vector<string> > vvs;
  separarjps(vs, vvs);
  v = vector<tvalor> (int(vvs.size()));
  for (int i = 0; i < int(vvs.size()); i++)
    leerjp(vvs[i], v[i], format);
}

void escribirtnodo(tnodo &nodo, int identacion)
{
  cout << string(identacion, ' ') << nodo.tipo;
  if (nodo.texto != "") cout << "(" << nodo.texto << ")";
  cout << endl;
  for (int i = 0; i < int(nodo.hijo.size()); i++)
    escribirtnodo(nodo.hijo[i], identacion + 2);
}

void escribirtnodo(tnodo &nodo)
{
  escribirtnodo(nodo, 0);
}

void leerprograma(string ficheroprograma, tnodo &nodo,
                  string internalerroringles, string internalerrorespanyol, string internalerrorcatalan)
{
  prefijoerroringles = internalerroringles;
  prefijoerrorespanyol = internalerrorespanyol;
  prefijoerrorcatalan = internalerrorcatalan;
  vector<string> vs = leerfichero(ficheroprograma);
  vector<ttoken> vt;
  leerentrada(vs, vt);
  if (int(vt.size()) > limitenumtokens)
    errorprogramademasiadogrande();
  /*
  for (int i=0;i<int(vt.size());i++)
    cout<<"("<<i<<" "<<vt[i].tipo<<" "<<vt[i].linea<<" "<<vt[i].columna<<")";
  cout<<endl;
  */
  int ivt = 0;
  parsing(nodo, vt, ivt);
  //escribirtnodo(nodo);
  if (ivt < int(vt.size()))
    errorcosasdespuesdelprograma(vt[ivt].linea, vt[ivt].columna);
}

void leerprogramas(string ficheroprograma, tnodo &nodo1, tnodo &nodo2)
{
  prefijoerroringles = "";
  prefijoerrorespanyol = "";
  prefijoerrorcatalan = "";
  vector<string> vs = leerfichero(ficheroprograma);
  vector<ttoken> vt;
  leerentrada(vs, vt);
  if (int(vt.size()) > limitenumtokens)
    errorprogramademasiadogrande();
  int ivt = 0;
  parsing(nodo1, vt, ivt);
  parsing(nodo2, vt, ivt);
  if (ivt < int(vt.size()))
    errorcosasdespuesdelprograma(vt[ivt].linea, vt[ivt].columna);
}

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
// Programa principal:

string sformatjp = "array of array of int";
string sformatsat = "array of array of string";
string sformatvalidador = "struct { valid:int english:string spanish:string catalan:string }";

int main(int argc, char *argv[])
{
  if (argc!=7)
    rechazar("Internal error: the number of arguments received by the judge is not correct.");

  string ficherojp = argv[1];
  string ficherojp2input = argv[2];
  string ficheroinput2sat = argv[3];
  string ficheropropuestasolucion = argv[4];
  string ficherovalidador = argv[5];
  string ficheroformat = argv[6];

  timer tlectura;
  tnodo formatjp, formatinput, formatsat, formatsolucion, formatvalidador;
  leerformatstring(sformatjp, formatjp);
  leerformatstring(sformatsat, formatsat);
  leerformatsfichero(ficheroformat, formatinput, formatsolucion);
  leerformatstring(sformatvalidador, formatvalidador);
  
  vector<tvalor> vjp;
  leerjps(ficherojp, vjp, formatjp);
  tnodo nodojp2input, nodoinput2sat, nodopropuestasolucion2sat, nodopropuestasolucion2solucion, nodovalidador;
  leerprograma(ficherojp2input, nodojp2input,
               "Internal error reading jp2input: " + ficherojp2input + "\n",
               "Error interno leyendo jp2input: " + ficherojp2input + "\n",
               "Error intern llegint jp2input: " + ficherojp2input + "\n");
  leerprograma(ficheroinput2sat, nodoinput2sat,
               "Internal error reading input2sat: " + ficheroinput2sat + "\n",
               "Error interno leyendo input2sat: " + ficheroinput2sat + "\n",
               "Error intern llegint input2sat: " + ficheroinput2sat + "\n");
  leerprograma(ficherovalidador, nodovalidador,
               "Internal error reading validator: " + ficherovalidador + "\n",
               "Error interno leyendo validator: " + ficherovalidador + "\n",
               "Error intern llegint validator: " + ficherovalidador + "\n");
  leerprogramas(ficheropropuestasolucion, nodopropuestasolucion2sat, nodopropuestasolucion2solucion);

  if (nodopropuestasolucion2sat.texto != "")
    morir("rejected", "The format of the program reducing to SAT should be: \"main { <instructions> }\".",
          "rechazado", "El formato del programa que reduce a SAT deberia ser: \"main { <instrucciones> }\".",
          "rebutjat", "El format del programa que redueix cap a SAT hauria de ser: \"main { <instruccions> }\".");
  if (nodopropuestasolucion2solucion.texto != "model")
    morir("rejected", "The format of the program that reconstructs the solution by analyzing the model should be: \"main(model) { <instructions> }\".",
          "rechazado", "El formato del programa que reconstruye la solucion a partir del model deberia ser: \"main(model) { <instrucciones> }\".",
          "rebutjat", "El format del programa que reconstrueix la solucio a partir del model hauria de ser: \"main(model) { <instruccions> }\".");  
  comprobarnoseusatipo(nodopropuestasolucion2sat, "out",
                       "the \"out\" variable cannot be directly accessed in a reduction to SAT,\nuse \"insertsat\" instead to create your formula.",
                       "la variable \"out\" no puede ser accedida directamente en una reduccion a SAT,\nen su lugar, utiliza \"insertsat\" para crear tu formula.",
                       "la variable \"out\" no pot ser accedida directament en una reduccio a SAT,\nen comptes d'aixo, utilitza \"insertsat\" per a crear la teva formula.");
  
  cout << "TIEMPO LECTURA Y PARSING = " << tlectura.elapsedstring() << endl;

  timer tejecucion1a;
  vector<tvalor> vinput, vsat1, vsat2;
  vector<string> muestrainput, muestraoutput;
  ejecuta(nodojp2input, vjp, vinput, formatinput,
          "Internal error running jp2input: " + ficherojp2input + "\n",
          "Error interno ejecutando jp2input: " + ficherojp2input + "\n",
          "Error intern executant jp2input: " + ficherojp2input + "\n",
          infinito);
  generamuestra(vinput, muestrainput, "  in");
  ejecuta(nodoinput2sat, vinput, vsat1, formatsat,
          "Internal error running input2sat: " + ficheroinput2sat + "\n",
          "Error interno ejecutando input2sat: " + ficheroinput2sat + "\n",
          "Error intern executant input2sat: " + ficheroinput2sat + "\n",
          infinito);
  vector<vector<string> > historialesinsertsat;
  timer tejecucion1b;
  ejecuta(nodopropuestasolucion2sat, vinput, vsat2, formatsat, "", "", "",
          finito, &historialesinsertsat);
  generamuestra(historialesinsertsat, muestraoutput, "  ");
  cout << "TIEMPO EJECUCION (to sat) = " << tejecucion1a.elapsedstring()
       << " (" << tejecucion1b.elapsedstring() << " en propuestasolucion, de los cuales " << fixed << setprecision(3) << tiempoinsertsat << "s son por los " << ejecucionesinsertsat << " insertsat)" << endl;
  sat_solver S1[vsat1.size()];
  sat_solver S2[vsat2.size()];
  vector<bool> resultados;
  ostringstream infoextensa[vjp.size()];
  double segaccum = 0.0;
  for (int i = 0; i < int(vjp.size()); i++) {
    timer t1;
    S1[i].add(vsat1[i]);
    bool respuestain = S1[i].solve();
    double segresolverin = t1.elapsed();
    timer t2;
    S2[i].add(vsat2[i]);
    bool respuestaout = S2[i].solve();
    double segresolverout = t2.elapsed();
    segaccum += segresolverin + segresolverout;
    infoextensa[i] << endl;
    infoextensa[i] << "############ JP " << (i + 1) << " ############" << endl;
    infoextensa[i] << "input is " << (respuestain ? "SAT" : "UNSAT")
                   << " vars=" << S1[i].numvars() << " clauses=" << vsat1[i].v.size()
                   << " time=" << fixed << setprecision(3) << segresolverin << "s" << endl;
    infoextensa[i] << "output is " << (respuestaout ? "SAT" : "UNSAT")
                   << " vars=" << S2[i].numvars() << " clauses=" << vsat2[i].v.size()
                   << " time=" << fixed << setprecision(3) << segresolverout << "s" << endl;
    infoextensa[i] << "vinput:" << endl;
    infoextensa[i] << muestrainput[i];
    if (respuestain != respuestaout) {
      cout << "TIEMPO SATSOLVING = " << fixed << setprecision(3) << segaccum << "s" << endl;
      for (int j = 0; j <= i; ++j)
        cout << infoextensa[j].str();
      if (respuestain and not respuestaout)
        errorrespuesta2SAT("positive", "positiva", "positiva", muestrainput[i], muestraoutput[i]);
      if (not respuestain and respuestaout) {
        if (argc == 7) {
          string muestrasolucion;
          tvalor validado;
          ejecutareconstruccion(nodopropuestasolucion2solucion, vinput[i], formatsolucion, &S2[i], muestrasolucion,
                                ficherovalidador, nodovalidador, formatvalidador, validado);
          errorrespuesta2SAT("negative", "negativa", "negativa", muestrainput[i], muestraoutput[i],
                             muestrasolucion, validado.m["english"].s, validado.m["spanish"].s, validado.m["catalan"].s);
        } else
          errorrespuesta2SAT("negative", "negativa", "negativa", muestrainput[i], muestraoutput[i]);
      }
    }
    resultados.push_back(respuestain);
  }
  cout << "TIEMPO SATSOLVING = " << fixed << setprecision(3) << segaccum << "s" << endl;

  timer tejecucion2;
  for (int i = 0; i < int(vjp.size()); i++) {
    if (not resultados[i]) continue;
    string muestrasolucion;
    tvalor validado;
    ejecutareconstruccion(nodopropuestasolucion2solucion, vinput[i], formatsolucion, &S2[i], muestrasolucion,
                          ficherovalidador, nodovalidador, formatvalidador, validado);
    infoextensa[i] << "reconstruccion:" << endl;
    infoextensa[i] << muestrasolucion << endl;
    if (not validado.m["valid"].x)
      errorreconstruccion(validado.m["english"].s, validado.m["spanish"].s, validado.m["catalan"].s,
                          muestrainput[i], muestrasolucion);
  }
  cout << "TIEMPO EJECUCION (reconstruccion, validacion) = " << tejecucion2.elapsedstring() << endl;
  for (int j = 0; j < int(vjp.size()); ++j)
    cout << infoextensa[j].str();
  prefijoerroringles = prefijoerrorespanyol = prefijoerrorcatalan = "";
  mensajeaceptacionconreconstruccion();
}
