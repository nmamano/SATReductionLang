// Written by Carles Creus, Guillem Godoy, Nil Mamano


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

bool DBG_MODE = false;

//set this to false to make diffs directly between outputs
bool OUTPUT_RUNTIMES = false;

string inprefix = "__in__";
string outprefix = "__out__";
string jpstring = "jp";

//using char "}" because it cannot be parsed correctly,
//so there are no conflicts with the user's logic variables' names
char neglitchar = '}';

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
  return static_cast<ostringstream*>( &(ostringstream() << x) )->str();
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

void morirpuro(string mensajecorto, string mensajelargo)
{
  // Pendiente de saber los nombres de los ficheros.
  {
    ofstream corto("answer");
    corto << mensajecorto << endl;
    corto.close();
    ofstream largo("answer.long");
    largo << mensajelargo << endl;
    largo.close();
  }
  exit(0);
}

string prefijoerror;

void rechazar(string mensajelargo) {
  string mensaje = prefijoerror + mensajelargo;
  morirpuro("rejected", mensaje);
}

void rechazar(int linea, int columna, string mensajelargo) {
  rechazar("Error line " + itos(linea) + " column " + itos(columna) + ": " + mensajelargo);
}

void rechazarruntime(int linea, int columna, string mensajelargo) {
  rechazar("Runtime error line " + itos(linea) + " column " + itos(columna) + ": " + mensajelargo);
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
    rechazar("Error when opening " + nombrefichero);
  }
  return v;
}

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Analisis lexico del programa de entrada:

bool isfield(string s, const vector<string>& fields) {
  for (string f : fields) if (s == f) return true;
  return false;
}

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

set<string> palabrasclaveprograma = {"main", "stop",
                                 "if", "else", "while", "for", "foreach",
                                 "and", "or", "not", "push", "size",
                                 "back", "min", "max", "abs", "in", //case: for i in v
                                 "reduction", "reconstruction",
                                 "iff", "implies", "atleast", "atmost", "exactly"};
set<string> cadenasclaveprograma = {"{", "}", "(", ")", "[", "]", "+", "-", "*", "/",
                            "%", "=", "&=", "==", "<", ">", "<=", ">=", "!=",
                            ";", ".", ",", "//", "++", "--", ".."};

void leeridentificador(const string &s, int &is, vector<ttoken> &vt, int linea, int desplazamientocolumna,
  const set<string>& palabrasclave, const vector<string>& infields, const vector<string>& outfields)
{
  int nextis = is;
  while (nextis < int(s.size()) and
         (esletra(s[nextis]) or esnumero(s[nextis]) or s[nextis] == '_'))
    nextis++;
  string id = s.substr(is, nextis - is);
  if (palabrasclave.count(id)) {
    vt.push_back(ttoken(id, "", linea, is + 1 + desplazamientocolumna));
  } else if (isfield(id, infields) and (vt.size() == 0 or vt[vt.size()-1].tipo != ".")) {
    //the second condition is for cases such as input:
    //struct { teachers: int subjects: struct { teachers: array of int } }
    vt.push_back(ttoken(inprefix, "", linea, is + 1 + desplazamientocolumna));
    vt.push_back(ttoken(".", "", linea, is + 1 + desplazamientocolumna));
    vt.push_back(ttoken("identificador", id, linea, is + 1 + desplazamientocolumna));
  } else if (isfield(id, outfields) and (vt.size() == 0 or vt[vt.size()-1].tipo != ".")) {
    vt.push_back(ttoken("outprefix", "", linea, is + 1 + desplazamientocolumna));
    vt.push_back(ttoken(".", "", linea, is + 1 + desplazamientocolumna));
    vt.push_back(ttoken("identificador", id, linea, is + 1 + desplazamientocolumna));
  } else {
    vt.push_back(ttoken("identificador", id, linea, is + 1 + desplazamientocolumna));
  }
  is = nextis;
}

int limitenumdigitos = 9;
string simplerProgramMsg = "This does not mean your program is wrong, but you should find a simpler one.";

void leerconstante(const string &s, int &is, vector<ttoken> &vt, int linea, int desplazamientocolumna)
{
  int nextis = is;
  while (nextis<int(s.size()) and esnumero(s[nextis])) nextis++;
  if (nextis - is >= limitenumdigitos)
    rechazar(linea, is + 1 + desplazamientocolumna, "the constant \"" + s.substr(is, nextis - is) + "\" is too big.\n" +
          simplerProgramMsg);
  vt.push_back(ttoken("constant", s.substr(is, nextis - is), linea, is + 1 + desplazamientocolumna));
  is = nextis;
}

void leerstringentrada(const string &s, vector<ttoken> &vt, int linea, int desplazamientocolumna,
  const vector<string>& infields, const vector<string>& outfields);

void leerstring(const string &s, int &is, vector<ttoken> &vt, int linea, int desplazamientocolumna,
  const vector<string>& infields, const vector<string>& outfields)
{
  int isini = is; //isini apunta a las comillas de abrir
  int nextis = is + 1;
  while (nextis < int(s.size()) and s[nextis] != '"')
    nextis++;
  if (nextis == int(s.size()))
    rechazar(linea, is + 1 + desplazamientocolumna, "the SAT variable should end in this line with '\"'.");
  nextis++;
  is = nextis; //is apunta al simbolo siguiente a las comillas de cerrar
  if (nextis - isini == 2) { //string vacio
    vt.push_back(ttoken("string", "", linea, isini + 1 + desplazamientocolumna));
    is = nextis;
    return;
  }
  string ss = s.substr(isini + 1, nextis - isini - 2); //todo lo que hay entre comillas
  int iss = 0;
  int columnacomillasabrir = isini + 1 + desplazamientocolumna;
  while (iss < int(ss.size()) and ss[iss] != '{' and ss[iss] != '}') iss++;
  int columnacorcheteabrir = columnacomillasabrir + 1 + iss; //+1 para saltar las comillas
  if (iss == int(ss.size()))
    vt.push_back(ttoken("string", ss, linea, columnacomillasabrir));
  else {
    if (ss[iss] == '}')
      rechazar(linea, columnacorcheteabrir, "the symbol '}' inside '\"...\"' should have the corresponding previous '{'.");
    iss++;
    vt.push_back(ttoken("stringini", ss.substr(0, iss), linea, columnacomillasabrir)); //stringini incluye el '{' final
    for (;;) { //invariante: iss apunta al simbolo siguiente de '{', columnacorchete corresponde a la columna del '{'
      int iss2 = iss;
      while (iss2 < int(ss.size()) and ss[iss2] != '{' and ss[iss2] != '}') iss2++;
      if (iss2 == int(ss.size()) or ss[iss2] == '{')
        rechazar(linea, columnacorcheteabrir, "the symbol '{' inside '\"...\"' should have the corresponding following '}'.");
      leerstringentrada(ss.substr(iss, iss2 - iss), vt, linea, columnacorcheteabrir + 1, infields, outfields);
      iss = iss2; //ahora iss apunta al simbolo '}'
      int columnacorchetecerrar = columnacomillasabrir + 1 + iss;
      iss2++;
      while (iss2 < int(ss.size()) and ss[iss2] != '{' and ss[iss2] != '}') iss2++;
      if (iss2 == int(ss.size())) {
        vt.push_back(ttoken("stringfin", ss.substr(iss), linea, columnacorchetecerrar));
        return;
      }
      if (ss[iss2] == '}')
        rechazar(linea, columnacomillasabrir + 1 + iss2, "the symbol '}' inside '\"...\"' should have the corresponding previous '{'.");
      columnacorcheteabrir = columnacomillasabrir + 1 + iss2;
      iss2++;
      vt.push_back(ttoken("stringmid", ss.substr(iss, iss2 - iss), linea, columnacorchetecerrar));
      iss = iss2;
    }
  }
}

void leertoken(const string &s, int &is, vector<ttoken> &vt, int linea, int desplazamientocolumna,
  const set<string>& palabrasclave, const set<string>& cadenasclave,
  const vector<string>& infields = vector<string>(), const vector<string>& outfields = vector<string>())
{
  if (esletra(s[is]) or (s[is] == '_')) {
    leeridentificador(s, is, vt, linea, desplazamientocolumna, palabrasclave, infields, outfields);
    return;
  }
  else if (esnumero(s[is])) {
    leerconstante(s, is, vt, linea, desplazamientocolumna);
    return;
  }
  else if (s[is] == '"') {
    leerstring(s, is, vt, linea, desplazamientocolumna, infields, outfields);
    return;
  }
  else {
    for (set<string>::reverse_iterator it = cadenasclave.rbegin(); it != cadenasclave.rend(); ++it) {
      string c = *it;
      if (int(s.size()) >= is + int(c.size()) and s.substr(is, int(c.size())) == c) {
        if (c == "//") {
          is = int(s.size());
        }
        else {
          vt.push_back(ttoken(c, "", linea, is + 1 + desplazamientocolumna));
          is += int(c.size());
        }
        return;
      }
    }
  }
  rechazar(linea, is + 1 + desplazamientocolumna, "there is no correspondence for \"" + s.substr(is) + "\"");
}

void saltarblancos(const string &s, int &i)
{
  while (i < int(s.size()) and (s[i] == ' ' or s[i] == '\t')) i++;
}

void leerstringentrada(const string &s, vector<ttoken> &vt, int linea, int desplazamientocolumna,
  const vector<string>& infields, const vector<string>& outfields)
{
  int is = 0;
  saltarblancos(s, is);
  while (is < int(s.size())) {
    leertoken(s, is, vt, linea, desplazamientocolumna, palabrasclaveprograma, cadenasclaveprograma, infields, outfields);
    saltarblancos(s, is);
  }
}

void leerentrada(vector<string> &vs, vector<ttoken> &vt,
  const vector<string>& infields, const vector<string>& outfields)
{
  for (int i = 0; i < int(vs.size()); i++) {
    leerstringentrada(vs[i], vt, i + 1, 0, infields, outfields);
  }
}

void verificarquenoseusa(string &s, vector<ttoken> &vt)
{
  for (ttoken& t : vt)
    if (t.tipo == s)
      rechazar(t.linea, t.columna, "it is not allowed to use \"" + s + "\".");
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
    rechazar(linea, columna, "the level of indexation is too big.");
}

void seesperabaver(vector<ttoken> &vt, int &ivt, string t)
{
  if (ivt == int(vt.size()))
    rechazar("Error: the end of the program was reached when we expected to see " + t + ".");
  string foundtype = vt[ivt].tipo;
  if (foundtype == "stringini") foundtype = "string";
  if (foundtype == "outprefix")
    rechazar(vt[ivt].linea, vt[ivt].columna, "we expected to see " + t + ", but we found " +
        "output variable \""+vt[ivt+2].texto+"\".");
  if (foundtype == inprefix)
    rechazar(vt[ivt].linea, vt[ivt].columna, "we expected to see " + t + ", but we found " +
        "input variable \""+vt[ivt+2].texto+"\".");
  rechazar(vt[ivt].linea, vt[ivt].columna, "we expected to see " + t + ", but we found \"" +
        foundtype + "\".");
}

void comprobartipo(vector<ttoken> &vt,int &ivt,string t)
{
  if (ivt==int(vt.size()) or vt[ivt].tipo!=t)
    seesperabaver(vt,ivt,"\""+t+"\"");
}

void saltartipo(vector<ttoken> &vt, int &ivt, string t)
{
  if (ivt == int(vt.size()) or vt[ivt].tipo != t)
    seesperabaver(vt, ivt, "\"" + t + "\"");
  ivt++;
}

string siguientetipo(vector<ttoken> &vt,int &ivt)
{
  if (ivt<int(vt.size())) return vt[ivt].tipo;
  return "";
}

void parsingexpresion(tnodo &nodo, vector<ttoken> &vt, int &ivt);
void parsingsumasrestas(tnodo &nodo,vector<ttoken> &vt,int &ivt);
void parsinginstruccion(tnodo &nodo, vector<ttoken> &vt, int &ivt);
void parsinglistainstrucciones(tnodo &nodo, vector<ttoken> &vt, int &ivt);

void parsingin(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  if (ivt == int(vt.size()) or (vt[ivt].tipo != "identificador" and vt[ivt].tipo != inprefix))
    seesperabaver(vt, ivt, "{\"ident\"}");
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
    seesperabaver(vt, ivt, "{\"-\",\"not\",\"ident\",\"constant\",\"string\",\"(\",\"abs\",\"min\",\"max\",\"atleast\",\"atmost\",\"exactly\",\"and\",\"or\"}");
  if (vt[ivt].tipo == "-" or vt[ivt].tipo == "not") {
    nodo = vt[ivt];
    nodo.hijo.push_back(tnodo());
    ivt++;
    parsingunarios(nodo.hijo[0], vt, ivt);
  } else if (vt[ivt].tipo == "constant" or vt[ivt].tipo == "string") {
    nodo = vt[ivt];
    ivt++;
  } else if (vt[ivt].tipo=="stringini") {
    nodo = tnodo("stringparametrizado", "", vt[ivt].linea, vt[ivt].columna);
    nodo.hijo.push_back(tnodo("string", vt[ivt].texto, vt[ivt].linea, vt[ivt].columna));
    ivt++;
    nodo.hijo.push_back(tnodo());
    parsingsumasrestas(nodo.hijo[1],vt,ivt);
    while(vt[ivt].tipo!="stringfin"){
      comprobartipo(vt, ivt, "stringmid");
      nodo.hijo.push_back(tnodo("string", vt[ivt].texto, vt[ivt].linea, vt[ivt].columna));
      ivt++;
      nodo.hijo.push_back(tnodo());
      parsingsumasrestas(nodo.hijo[nodo.hijo.size()-1],vt,ivt);
    }
    nodo.hijo.push_back(tnodo("string", vt[ivt].texto, vt[ivt].linea, vt[ivt].columna));
    ivt++;
  } else if (vt[ivt].tipo == "abs") {
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (1);
    ivt++;
    saltartipo(vt, ivt, "(");
    parsingexpresion(nodo.hijo[0], vt, ivt);
    saltartipo(vt, ivt, ")");
  } else if (vt[ivt].tipo == "max" or vt[ivt].tipo == "min") {
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
  } else if (vt[ivt].tipo == "identificador" or vt[ivt].tipo == inprefix) {
    parsingin(nodo, vt, ivt);
  } else if (vt[ivt].tipo == "outprefix") {
    rechazar(vt[ivt].linea, vt[ivt].columna, "cannot read from output variable " + vt[ivt+2].texto + ".");
  } else if (vt[ivt].tipo == "and" or vt[ivt].tipo == "or") {
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (1);
    ivt++;
    parsinglistainstrucciones(nodo.hijo[0], vt, ivt);
  } else if (vt[ivt].tipo == "exactly" or vt[ivt].tipo == "atmost" or vt[ivt].tipo == "atleast") {
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (2);
    ivt++;
    parsingexpresion(nodo.hijo[0], vt, ivt);
    parsinglistainstrucciones(nodo.hijo[1], vt, ivt);
  } else
    seesperabaver(vt, ivt, "{\"not\",\"-\",\"ident\",\"constant\",\"string\",\"(\",\"abs\",\"min\",\"max\",\"atleast\",\"atmost\",\"exactly\",\"and\",\"or\"}");
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

void parsingand(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  parsingcomparaciones(nodo, vt, ivt);
  while (ivt < int(vt.size()) and (vt[ivt].tipo == "and")) {
    tnodo nodoaux = nodo;
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (2);
    nodo.hijo[0] = nodoaux;
    ivt++;
    parsingcomparaciones(nodo.hijo[1], vt, ivt);
  }
}

void parsingor(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  parsingand(nodo, vt, ivt);
  while (ivt < int(vt.size()) and (vt[ivt].tipo == "or")) {
    tnodo nodoaux = nodo;
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (2);
    nodo.hijo[0] = nodoaux;
    ivt++;
    parsingand(nodo.hijo[1], vt, ivt);
  }
}

void parsingimpl(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  parsingor(nodo, vt, ivt);
  if (ivt < int(vt.size()) and (vt[ivt].tipo == "implies")) { //not associative
    tnodo nodoaux = nodo;
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (2);
    nodo.hijo[0] = nodoaux;
    ivt++;
    parsingor(nodo.hijo[1], vt, ivt);
  }
}

void parsingexpresion(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  parsingimpl(nodo, vt, ivt);
  if (ivt < int(vt.size()) and (vt[ivt].tipo == "iff")) { //not associative
    tnodo nodoaux = nodo;
    nodo = vt[ivt];
    nodo.hijo = vector<tnodo> (2);
    nodo.hijo[0] = nodoaux;
    ivt++;
    parsingimpl(nodo.hijo[1], vt, ivt);
  }
}

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
  if (ivt == int(vt.size()) or vt[ivt].tipo != "outprefix")
    seesperabaver(vt, ivt, "ident");
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

//ivt points to the next token after 'for' (which is not '(')
void parsingforeach(tnodo &nodo,vector<ttoken> &vt,int &ivt) {
  nodo = tnodo("foreach", "", vt[ivt-1].linea, vt[ivt-1].columna);
  comprobartipo(vt,ivt,"identificador");
  nodo.hijo.push_back(vt[ivt]);
  ivt++;
  bool tieneindice = false;
  if (siguientetipo(vt,ivt)==",") {
    tieneindice = true;
    saltartipo(vt,ivt,",");
    comprobartipo(vt,ivt,"identificador");
    nodo.hijo.push_back(vt[ivt]);
    ivt++;
  }
  saltartipo(vt,ivt,"in");
  tnodo e1;
  parsingsumasrestas(e1,vt,ivt);
  if (siguientetipo(vt,ivt)=="..") {
    if (tieneindice)
      rechazar(vt[ivt].linea, vt[ivt].columna, "a for loop over a range of the form x..y does not have an index");
    saltartipo(vt,ivt,"..");
    tnodo e2;
    parsingsumasrestas(e2,vt,ivt);
    nodo.hijo.push_back(tnodo());
    nodo.hijo.back().tipo="..";
    nodo.hijo.back().hijo.push_back(e1);
    nodo.hijo.back().hijo.push_back(e2);
  } else {
    nodo.hijo.push_back(e1);
  }
  if (siguientetipo(vt,ivt)==",") {
    ivt++;
    nodo.hijo.push_back(tnodo());
    parsingforeach(nodo.hijo.back(),vt,ivt);
  } else {
    nodo.hijo.push_back(tnodo());
    parsinginstruccion(nodo.hijo.back(),vt,ivt);
  }
}

void parsinginstruccion(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  if (ivt == int(vt.size()))
    seesperabaver(vt, ivt, "{\"if\",\"ident\",\"++\",\"--\",\"{\",\"while\",\"for\",\"stop\",\"expr\"}");
  if (vt[ivt].tipo == "if") {
    nodo = vt[ivt];
    ivt++;
    saltartipo(vt, ivt, "(");
    nodo.hijo.push_back(tnodo());
    parsingexpresion(nodo.hijo[0], vt, ivt);
    //the error message generated by saltartipo here is incomplete in the reconstruction, because after
    //an expression there could be "or", "and", "implies" or "iff" besides ")"
    //(we would have parsed it, but the user does not know that)
    //case: if ("x" "y") ..
    //generated error: expected ")", found "string"
    //complete error: expected {")","and","or","implies","iff"}, found "string"
    //I don't think it is important... and fixing it requires the parser to know if
    //it is inside a reconstruction, which it does not at the moment, so it can stay like this
    saltartipo(vt, ivt, ")");
    nodo.hijo.push_back(tnodo());
    parsinginstruccion(nodo.hijo[1], vt, ivt);
    if (ivt < int(vt.size()) and vt[ivt].tipo == "else") {
      ivt++;
      nodo.hijo.push_back(tnodo());
      parsinginstruccion(nodo.hijo[2], vt, ivt);
    }
  } else if (vt[ivt].tipo == ";" or vt[ivt].tipo == "++" or vt[ivt].tipo == "--") {
    parsingasignacionsimple(nodo, vt, ivt, ";");
  } else if (vt[ivt].tipo == "identificador") {
    //do LL(2) parsing to see if we are inside an expression or an assignment
    if (ivt+1 == int(vt.size())) {
      rechazar(vt[ivt].linea, vt[ivt].columna, "Unexpected end of input");
    } else if (vt[ivt+1].tipo == "=" or vt[ivt+1].tipo == "&=" or
        vt[ivt+1].tipo == "++" or vt[ivt+1].tipo == "--") {
      parsingasignacionsimple(nodo, vt, ivt, ";");
    } else if (vt[ivt+1].tipo == "and" or vt[ivt+1].tipo == "or" or
        vt[ivt+1].tipo == "iff" or vt[ivt+1].tipo == "implies" or vt[ivt+1].tipo == ";") {
      parsingexpresion(nodo, vt, ivt);
      if (ivt == int(vt.size()) or vt[ivt].tipo != ";")
        seesperabaver(vt, ivt, "{\";\",\"or\",\"and\",\"implies\",\"iff\"}");
      ivt++;
    } else {
      rechazar(vt[ivt].linea, vt[ivt].columna, "Unexpected token after identifier");
    }
  } else if (vt[ivt].tipo == "atleast" or vt[ivt].tipo == "string" or
      vt[ivt].tipo == "exactly" or vt[ivt].tipo == "or" or vt[ivt].tipo == "not" or
      vt[ivt].tipo == "atmost" or vt[ivt].tipo == "and" or vt[ivt].tipo == "stringini" or
      vt[ivt].tipo == "(") {
    parsingexpresion(nodo, vt, ivt);
    if (ivt == int(vt.size()) or vt[ivt].tipo != ";")
      seesperabaver(vt, ivt, "{\";\",\"or\",\"and\",\"implies\",\"iff\"}");
    ivt++;
  } else if (vt[ivt].tipo == "outprefix") {
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
  } else if (vt[ivt].tipo == "for") {
    ivt++; //points to the token after for
    if (ivt == int(vt.size()) or (vt[ivt].tipo != "(" and vt[ivt].tipo != "identificador"))
      seesperabaver(vt, ivt, "{\"(\",\"ident\"}"); //looking at next token to discern for and foreach
    if (vt[ivt].tipo == "(") { //for normal
      nodo = vt[ivt-1];
      saltartipo(vt, ivt, "(");
      nodo.hijo = vector<tnodo> (4);
      parsingasignacionsimple(nodo.hijo[0], vt, ivt, ";");
      parsingexpresion(nodo.hijo[1], vt, ivt);
      saltartipo(vt, ivt, ";");
      parsingasignacionsimple(nodo.hijo[2], vt, ivt, ")");
      parsinginstruccion(nodo.hijo[3], vt, ivt);
    }
    else parsingforeach(nodo, vt, ivt);
  } else if (vt[ivt].tipo == "{") {
    parsinglistainstrucciones(nodo, vt, ivt);
  } else if (vt[ivt].tipo == "stop") {
    nodo = vt[ivt];
    ivt++;
    saltartipo(vt, ivt, ";");
  } else
    seesperabaver(vt, ivt, "{\"if\",\"ident\",\"++\",\"--\",\"{\",\"while\",\"for\",\"stop\",\"expr\"}");
}

void parsinglistainstrucciones(tnodo &nodo, vector<ttoken> &vt, int &ivt)
{
  nodo.tipo = "lista";
  saltartipo(vt, ivt, "{");
  while (ivt < int(vt.size()) and vt[ivt].tipo != "}") {
    nodo.hijo.push_back(tnodo());
    parsinginstruccion(nodo.hijo.back(), vt, ivt);
  }
  saltartipo(vt, ivt, "}");
}

void parsing(tnodo &nodo, vector<ttoken> &vt, int &ivt, string tipoprograma)
{
  if (ivt == int(vt.size()) or vt[ivt].tipo != tipoprograma) {
    if (tipoprograma == "main") rechazar("The program must have the format \"main { <instructions> }\"");
    else rechazar("The program must have the format \"reduction { <instructions> }    reconstruction { <instructions> }\"");
  }
  nodo = vt[ivt];
  nodo.hijo.push_back(tnodo());
  ivt++;
  parsinglistainstrucciones(nodo.hijo[0], vt, ivt);
}

void comprobarnoseusatipo(tnodo const &nodo, string const &tipo, string const &mensajeerror)
{
  if (nodo.tipo == tipo)
    rechazar(nodo.linea, nodo.columna, mensajeerror);
  for (int i = 0; i < int(nodo.hijo.size()); ++i)
    comprobarnoseusatipo(nodo.hijo[i], tipo, mensajeerror);
}

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
    rechazar("Runtime error: the program produces an overflow.\n" + simplerProgramMsg);
}

int limitesizestring = 20000;

void controllimitesizestring(string &s)
{
  if (int(s.size()) > limitesizestring)
    rechazar("Runtime error: the program produces a too big string.\n" + simplerProgramMsg);
}

struct tvalor {
  int kind; // 0=entero, 1=string, 2=vector de tvalor, 3=referencia a "in", 4=struct
  ll x;
  string s;
  vector<tvalor> v;
  tvalor *ref;
  tnodo *format;
  map<string, tvalor> m;
  string stringformula;

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

  bool esentero() { return kind == 0; }
  bool esstring() { return kind == 1; }

};

void valorpordefecto(tnodo &nodo, tvalor &valor)
{
  valor.format = &nodo;
  if (nodo.tipo == "int") {
    valor.kind = 0;
    valor.x = 0;
  } else if (nodo.tipo == "string") {
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
    rechazar("Execution error in default value: \"" + nodo.tipo + "\" is not a type.");
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
          //cerr<<"add "<<literal<<endl;
          if (not literal.empty() and literal[0] == neglitchar)
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
        rechazar("Runtime error: accessed the model with an unknown variable name: " + variable + ".");
      }
  #if defined(USE_MINISAT)
      using namespace Minisat;
      return (S.model[string_codes.find(variable)->second] == l_True);
  #elif defined(USE_PICOSAT)
      return (picosat_deref(S, 1 + string_codes.find(variable)->second) == 1);
  #endif
    }
    void printmodelo() {
  #if defined(USE_MINISAT)
      using namespace std;
      using namespace Minisat;
      for (auto &it : string_codes) {
        cout<<it.first<<": "<<flush;
        cout<<(S.model[it.second] == l_True)<<endl;
      }
  #elif defined(USE_PICOSAT)
  #endif
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
// Funciones auxiliares para las formulas logicas

bool storestringformula = false;

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
  if (int(s.size()) > 0 and s[0] == neglitchar) return s.substr(1);
  return string(1, neglitchar) + s;
}

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

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Ejecucion del programa de entrada:

enum Modo {
  reduc,
  recon,
  inter
};

Modo MODE;

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
    rechazar("Runtime error: the program uses too much memory.\n" + simplerProgramMsg);
}

tvalor comprobarentero(string op, tvalor v)
{
  if (v.kind != 0)
    rechazar("Runtime error: '" + op + "' should be applied to integers.");
  return v;
}

void comprobarentero(string op, tvalor v1, tvalor v2)
{
  if (v1.kind != 0 or v2.kind != 0)
    rechazar("Runtime error: '" + op + "' should be applied to integers.");
}

void comprobarstring(string op, tvalor v)
{
  if (v.kind != 1)
    rechazar("Runtime error: '" + op + "' should be applied to strings.");
}

void comprobarenteroostring(string op, tvalor v1, tvalor v2)
{
  if ((v1.kind != 0 and v1.kind != 1) or (v2.kind != 0 and v2.kind != 1))
    rechazar("Runtime error: '" + op + "' should be applied to integers or strings.");
}

void comprobarenteroostring(string op, tvalor v)
{
  if (v.kind != 0 and v.kind != 1)
    rechazar("Runtime error: '" + op + "' should be applied to integers or strings.");
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
    rechazar("Runtime error: '" + op + "' should not have second operand equal to 0.");
  return v1.x / v2.x;
}

tvalor operator%(tvalor v1, tvalor v2)
{
  comprobarentero("%", v1, v2);
  string op = "%";
  if (v2.x == 0)
    rechazar("Runtime error: '" + op + "' should not have second operand equal to 0.");
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

tvalor ejecutaexpresion(tnodo &nodo, tvalor &in, tvalor &out, map<string, tvalor> &valor, int &memoria,
                        sat_solver const *modelo);
int ejecutainstruccion(tnodo &nodo, tvalor &in, tvalor &out, map<string, tvalor> &valor, int &memoria,
            sat_solver const *modelo);

tvalor &extraerelemento(tnodo &nodo, tvalor &in, tvalor &out, map<string, tvalor> &valor, int &memoria,
                        sat_solver const *modelo)
{
  if (nodo.tipo == inprefix) return in;
  if (nodo.tipo == "identificador") {
    if (valor.count(nodo.texto) == 0)
      rechazarruntime(nodo.linea, nodo.columna, "using the variable \"" + nodo.texto + "\" when no value has been assigned to it.");
    tvalor v = valor[nodo.texto];
    if (v.kind != 3)
      rechazarruntime(nodo.linea, nodo.columna, nodo.texto + "is not a reference to the input here.");
    return *v.ref;
  }
  if (nodo.tipo == "[") {
    tvalor &v1 = extraerelemento(nodo.hijo[0], in, out, valor, memoria, modelo);
    tvalor v2 = ejecutaexpresion(nodo.hijo[1], in, out, valor, memoria, modelo);
    if (v1.kind != 2)
      rechazarruntime(nodo.linea, nodo.columna, "indexed access to a non-array.");
    comprobarentero("array[...]", v2);
    if (v2.x < 0 or int(v1.v.size()) <= v2.x)
      rechazarruntime(nodo.linea, nodo.columna, "out of range in array access.");
    return v1.v[v2.x];
  }
  if (nodo.tipo == "back") {
    tvalor &v1 = extraerelemento(nodo.hijo[0], in, out, valor, memoria, modelo);
    if (v1.kind != 2)
      rechazarruntime(nodo.linea, nodo.columna, "back access to a non-array.");
    if (int(v1.v.size()) == 0)
      rechazarruntime(nodo.linea, nodo.columna, "back access to an array with 0 size.");
    return v1.v.back();
  }
  if (nodo.tipo == ".") {
    tvalor &v1 = extraerelemento(nodo.hijo[0], in, out, valor, memoria, modelo);
    if (v1.kind != 4)
      rechazarruntime(nodo.linea, nodo.columna, "field access to a non-struct.");
    if (v1.m.count(nodo.texto) == 0)
      rechazarruntime(nodo.linea, nodo.columna, "the struct does not have a field called " + nodo.texto + ".");
    return v1.m[nodo.texto];
  }
  // Aquest error no s'hauria de donar mai:
  rechazarruntime(nodo.linea, nodo.columna, "an indexation to the input or output was expected.");
  return in;
}

string addtab(const string& s) {
  if (s == "") return s;
  string res = "  ";
  for (uint i = 0; i < s.size(); i++) {
    res.push_back(s[i]);
    if (s[i] == '\n' and i < s.size()-1) res += "  ";
  }
  return res;
}

/* The AST of stringparametrizado looks like this:
stringparametrizado
  string(x{)
  constante(1)
  string(})
Hence in the reconstruction we must not check the model with strings
that are part of a stringparametrizado */
bool insidestringparametrizado = false;

tvalor ejecutaexpresion(tnodo &nodo, tvalor &in, tvalor &out, map<string, tvalor> &valor, int &memoria,
                        sat_solver const *modelo)
{
  if (nodo.tipo == "identificador") {
    if (valor.count(nodo.texto) == 0)
      rechazarruntime(nodo.linea, nodo.columna, "using the variable \"" + nodo.texto + "\" when no value has been assigned to it.");
    if (valor[nodo.texto].kind == 3) {
      tvalor &v = *valor[nodo.texto].ref;
      if (v.kind != 0 and v.kind != 1)
        rechazarruntime(nodo.linea, nodo.columna, "only simple types inside the input can be accessed in an expression.");
      return v;
    }
    return valor[nodo.texto];
  } else if (nodo.tipo == "constant") {
    return stoll(nodo.texto);
  } else if (nodo.tipo == "string") {
    if (MODE == recon and not insidestringparametrizado) {
      return tvalor(modelo->assignment(nodo.texto));
    } else {
      tvalor t(nodo.texto);
      if (storestringformula) t.stringformula = nodo.texto;
      return t;
    }
  } else if (nodo.tipo == "stringparametrizado") {
    string substringsconcatenados = "";
    for (int i = 0; i < int(nodo.hijo.size()); i++) {
      insidestringparametrizado = true;
      tvalor v = ejecutaexpresion(nodo.hijo[i], in, out, valor, memoria, modelo);
      insidestringparametrizado = false;
      subirastring(v);
      substringsconcatenados += v.s;
    }
    if (MODE == recon) {
      return tvalor(modelo->assignment(substringsconcatenados));
    } else {
      tvalor t(substringsconcatenados);
      if (storestringformula) t.stringformula = substringsconcatenados;
      return t;
    }
  } else if (nodo.tipo == "size") {
    tvalor &v = extraerelemento(nodo.hijo[0], in, out, valor, memoria, modelo);
    if (v.kind != 2)
      rechazarruntime(nodo.linea, nodo.columna, "\"size\" must be applied to an array.");
    return int(v.v.size());
  } else if (nodo.tipo == inprefix or nodo.tipo == "back" or nodo.tipo == "[" or nodo.tipo == ".") {
    tvalor &v = extraerelemento(nodo, in, out, valor, memoria, modelo);
    if (v.kind != 0 and v.kind != 1)
      rechazarruntime(nodo.linea, nodo.columna, "only simple types inside the input can be accessed in an expression.");
    return v;
  } else if (nodo.tipo == "abs") {
    return abs(ejecutaexpresion(nodo.hijo[0], in, out, valor, memoria, modelo));
  } else if (nodo.tipo == "and") {
    if (nodo.hijo.size() == 2) { // binary case
      tvalor hijo1 = ejecutaexpresion(nodo.hijo[0], in, out, valor, memoria, modelo);
      if (hijo1.esentero() and hijo1.x == 0) return 0; //lazy evaluation
      tvalor hijo2 = ejecutaexpresion(nodo.hijo[1], in, out, valor, memoria, modelo);
      if (hijo1.esentero() and hijo2.esentero()) {
        return hijo1.x != 0 and hijo2.x != 0;
      } else if (hijo1.esstring() and hijo2.esstring()) {
        if (MODE == reduc) {
          string id = generaid();
          out.v.push_back(tvalor(tvalor(id), tvalor(negar(hijo1.s)), tvalor(negar(hijo2.s))));
          out.v.push_back(tvalor(tvalor(negar(id)), hijo1.s));
          out.v.push_back(tvalor(tvalor(negar(id)), hijo2.s));
          tvalor t(id);
          if (storestringformula)
            t.stringformula = "and (\n"+addtab(hijo1.stringformula)+"\n"+addtab(hijo2.stringformula)+"\n)";
          return t;
        }
        else {
          rechazarruntime(nodo.linea, nodo.columna, "Cannot apply \"and\" to strings");
        }
      } else {
        rechazarruntime(nodo.linea, nodo.columna, "Uncompatible operands of \"and\"");
      }
    } else if (MODE == reduc and nodo.hijo.size() == 1 and nodo.hijo[0].tipo == "lista") { //scope expression case
      tvalor scopeout;
      scopeout.format = out.format;
      ejecutainstruccion(nodo.hijo[0], in, scopeout, valor, memoria, modelo); //ignoramos el valor de retorno?
      vector<string> sol;
      for (tvalor &clause : scopeout.v) {
        //las clausulas de 1 elemento contienen las variables afirmadas dentro del scope
        if (clause.v.size() == 1) sol.push_back(clause.v[0].s);
        //las demas clausulas son las que les dan el significado apropiado
        else out.v.push_back(clause);
      }
      if (int(sol.size()) == 0) {
        string id = generaid();
        tvalor valor;
        valor.kind = 2;
        valor.v.push_back(tvalor(id));
        valor.v.push_back(tvalor(id));
        /* Why is id added 2 times in the same clause?
        See comment for the or case
        */
        out.v.push_back(valor);
        tvalor t(id);
        if (storestringformula) t.stringformula = "and {\n" + addtab(scopeout.stringformula) + "}";
        return t;
      }
      if (int(sol.size()) == 1) {
        tvalor t(sol[0]);
        if (storestringformula) t.stringformula = "and {\n" + addtab(scopeout.stringformula) + "}";
        return t;
      }
      string id = generaid();
      tvalor valor;
      valor.kind = 2;
      valor.v.push_back(tvalor(id));
      for (int i = 0; i < int(sol.size()); i++) {
        out.v.push_back(tvalor(tvalor(negar(id)), tvalor(sol[i])));
        valor.v.push_back(tvalor(negar(sol[i])));
      }
      out.v.push_back(valor);
      tvalor t(id);
      if (storestringformula) t.stringformula = "and {\n" + addtab(scopeout.stringformula) + "}";
      return t;
    } else {
      rechazarruntime(nodo.linea, nodo.columna, "invalid arguments for \"and\"");
    }
  } else if (nodo.tipo == "or") {
    if (nodo.hijo.size() == 2) { // binary case
      tvalor hijo1 = ejecutaexpresion(nodo.hijo[0], in, out, valor, memoria, modelo);
      if (hijo1.esentero() and hijo1.x != 0) return 1; //lazy evaluation
      tvalor hijo2 = ejecutaexpresion(nodo.hijo[1], in, out, valor, memoria, modelo);
      if (hijo1.esentero() and hijo2.esentero()) {
        return hijo1.x != 0 or hijo2.x != 0;
      } else if (hijo1.esstring() and hijo2.esstring()) {
        if (MODE == reduc) {
          string id = generaid();
          out.v.push_back(tvalor(tvalor(negar(id)), tvalor(hijo1.s), tvalor(hijo2.s)));
          out.v.push_back(tvalor(tvalor(id), tvalor(negar(hijo1.s))));
          out.v.push_back(tvalor(tvalor(id), tvalor(negar(hijo2.s))));
          tvalor t(id);
          if (storestringformula)
            t.stringformula = "or (\n"+addtab(hijo1.stringformula)+"\n"+addtab(hijo2.stringformula)+"\n)";
          return t;
        }
        else {
          rechazarruntime(nodo.linea, nodo.columna, "Cannot apply \"or\" to strings");
        }
      } else {
        rechazarruntime(nodo.linea, nodo.columna, "Uncompatible operands of \"or\"");
      }
    } else if (MODE == reduc and nodo.hijo.size() == 1 and nodo.hijo[0].tipo == "lista") {
      tvalor scopeout;
      scopeout.format = out.format;
      ejecutainstruccion(nodo.hijo[0], in, scopeout, valor, memoria, modelo); //ignoramos el valor de retorno?
      vector<string> sol;
      for (tvalor &clause : scopeout.v) {
        //las clausulas de 1 elemento contienen las variables afirmadas dentro del scope
        if (clause.v.size() == 1) sol.push_back(clause.v[0].s);
        //las demas clausulas son las que les dan el significado apropiado
        else out.v.push_back(clause);
      }
      if (int(sol.size()) == 0) {
        string id = generaid();
        tvalor valor;
        valor.kind = 2;
        valor.v.push_back(tvalor(negar(id)));
        valor.v.push_back(tvalor(negar(id)));
        /* Why is negar(id) added 2 times in the same clause?
        Because the rule with expression-scopes is that clauses with a single variable
        contain variables that are logically equivalent to an explicitly stated formula,
        such as '"x" or "y"' in: 'or { "x" or "y"; };'
        while clauses with more than one variable are the clausules needed to enforce the meaning
        of these variables.
        In this case, id is the variable equivalent to the stated empty or, and it should be
        logically equivalent to false. Hence, we need to enforce negar(id).
        We add it two times to show that it is not a stated formula.

        This should be refactorized, dotating variables with an attribute
        "stated" or "auxiliar"
        */
        out.v.push_back(valor);
        tvalor t(id);
        if (storestringformula) t.stringformula = "or {\n" + addtab(scopeout.stringformula) + "}";
        return t;
      }
      if (int(sol.size()) == 1) {
        tvalor t(sol[0]);
        if (storestringformula) t.stringformula = "or {\n" + addtab(scopeout.stringformula) + "}";
        return t;
      }
      string id = generaid();
      tvalor valor;
      valor.kind = 2;
      valor.v.push_back(tvalor(negar(id)));
      for (int i = 0; i < int(sol.size()); i++) {
        out.v.push_back(tvalor(tvalor(id), tvalor(negar(sol[i]))));
        valor.v.push_back(tvalor(sol[i]));
      }
      out.v.push_back(valor);
      tvalor t(id);
      if (storestringformula) t.stringformula = "or {\n" + addtab(scopeout.stringformula) + "}";
      return t;
    } else {
      rechazarruntime(nodo.linea, nodo.columna, "invalid arguments for \"or\"");
    }
  } else if (nodo.tipo == "implies") {
      tvalor hijo1 = ejecutaexpresion(nodo.hijo[0], in, out, valor, memoria, modelo);
      tvalor hijo2 = ejecutaexpresion(nodo.hijo[1], in, out, valor, memoria, modelo);
      if (MODE == reduc) {
      if (not hijo1.esstring() or not hijo2.esstring())
        rechazarruntime(nodo.linea, nodo.columna, "\"implies\" must be aplied to logical formulas");
      string id = generaid();
      out.v.push_back(tvalor(tvalor(negar(id)), tvalor(negar(hijo1.s)), tvalor(hijo2.s)));
      out.v.push_back(tvalor(tvalor(id), tvalor(hijo1.s)));
      out.v.push_back(tvalor(tvalor(id), tvalor(negar(hijo2.s))));
      tvalor t(id);
      if (storestringformula) t.stringformula = hijo1.stringformula+" implies "+hijo2.stringformula;
      return t;
    } else if (MODE == recon) {
      if (not hijo1.esentero() or not hijo2.esentero()) {
        rechazarruntime(nodo.linea, nodo.columna, "\"implies\" must be applied to logical formulas");
      }
      if (hijo1.x == 0) return 1;
      return hijo2.x != 0;
    }
  } else if (nodo.tipo == "iff") {
    tvalor hijo1 = ejecutaexpresion(nodo.hijo[0], in, out, valor, memoria, modelo);
    tvalor hijo2 = ejecutaexpresion(nodo.hijo[1], in, out, valor, memoria, modelo);
    if (MODE == reduc) {
      if (not (hijo1.esstring() and hijo2.esstring()))
        rechazarruntime(nodo.linea, nodo.columna, "\"iff\" must be aplied to logical formulas");
      string id = generaid();
      out.v.push_back(tvalor(tvalor(id), tvalor(negar(hijo1.s)), tvalor(negar(hijo2.s))));
      out.v.push_back(tvalor(tvalor(id), tvalor(hijo1.s), tvalor(hijo2.s)));
      out.v.push_back(tvalor(tvalor(negar(id)), tvalor(negar(hijo1.s)), tvalor(hijo2.s)));
      out.v.push_back(tvalor(tvalor(negar(id)), tvalor(hijo1.s), tvalor(negar(hijo2.s))));
      tvalor t(id);
      if (storestringformula) t.stringformula = hijo1.stringformula+" iff "+hijo2.stringformula;
      return t;
    } else if (MODE == recon) {
      if (not hijo1.esentero() or not hijo2.esentero()) {
        rechazarruntime(nodo.linea, nodo.columna, "\"iff\" must be applied to logical formulas");
      }
      if (hijo1.x == 0) return hijo2.x == 0;
      return hijo2.x != 0;
    }
  } else if (nodo.tipo == "atmost" or nodo.tipo == "atleast" or nodo.tipo == "exactly") {
    if (MODE != reduc)
      rechazarruntime(nodo.linea, nodo.columna, nodo.tipo+" can only appear in a reduction");
    tvalor count = ejecutaexpresion(nodo.hijo[0], in, out, valor, memoria, modelo);
    if (not count.esentero()) {
      rechazarruntime(nodo.hijo[0].linea, nodo.hijo[0].columna, nodo.tipo+" must be followed by a number");
    } else if (count.x < 0) {
      rechazarruntime(nodo.hijo[0].linea, nodo.hijo[0].columna, nodo.tipo+" expects a non-negative integer");
    }
    tvalor scopeout;
    scopeout.format = out.format;
    ejecutainstruccion(nodo.hijo[1], in, scopeout, valor, memoria, modelo); //ignoramos el valor de retorno?
    vector<string> sol;
    for (tvalor &clause : scopeout.v) {
      //las clausulas de 1 elemento contienen las variables afirmadas dentro del scope
      if (clause.v.size() == 1) sol.push_back(clause.v[0].s);
      //las demas clausulas son las que les dan el significado apropiado
      else out.v.push_back(clause);
    }
    string id = ladderencoding(nodo.tipo, count.x, sol, out);
    tvalor t(id);
    if (storestringformula) t.stringformula = nodo.tipo+" "+itos(count.x)+" {\n"+addtab(scopeout.stringformula)+"}";
    return t;
  } else {
    tvalor v[2];
    for (int i = 0; i < int(nodo.hijo.size()); i++)
      v[i] = ejecutaexpresion(nodo.hijo[i], in, out, valor, memoria, modelo);
    if (nodo.tipo == "-") {
      if (int(nodo.hijo.size()) == 1) return -v[0].x;
      return v[0] - v[1];
    }
    if (nodo.tipo == "max") return max(v[0], v[1]);
    if (nodo.tipo == "min") return min(v[0], v[1]);
    if (nodo.tipo == "+") {
      if (MODE == reduc and (v[0].esstring() or v[1].esstring()))
        rechazarruntime(nodo.linea, nodo.columna, "Invalid operands on \"+\"");
      return v[0] + v[1];
    }
    if (nodo.tipo == "*") return v[0] * v[1];
    if (nodo.tipo == "/") return v[0] / v[1];
    if (nodo.tipo == "%") return v[0] % v[1];
    if (nodo.tipo == "==") return v[0] == v[1];
    if (nodo.tipo == "!=") return v[0] != v[1];
    if (nodo.tipo == "<") return v[0] < v[1];
    if (nodo.tipo == ">") return v[0] > v[1];
    if (nodo.tipo == "<=") return v[0] <= v[1];
    if (nodo.tipo == ">=") return v[0] >= v[1];
    if (nodo.tipo == "not") {
      if (v[0].esentero()) return !v[0];
      if (v[0].esstring()) {
        if (MODE == reduc) {
          tvalor t(negar(v[0].s));
          if (storestringformula) t.stringformula = "not "+v[0].stringformula;
          return t;
        }
      }
      rechazarruntime(nodo.linea, nodo.columna, "Invalid operand on \"not\"");
    }
  }
  return 0;
}

tvalor &extraerout(tnodo &nodo, tvalor &in, tvalor &out, map<string, tvalor> &valor, int &memoria,
                   sat_solver const *modelo)
{
  if (nodo.tipo == "outprefix") return out;
  tvalor &v1 = extraerout(nodo.hijo[0], in, out, valor, memoria, modelo);
  if (nodo.tipo == ".") {
    if (v1.kind != 4)
      rechazarruntime(nodo.linea, nodo.columna, "field access to a non-struct.");
    if (v1.m.count(nodo.texto) == 0)
      rechazarruntime(nodo.linea, nodo.columna, "the struct does not have a field called " + nodo.texto + ".");
    return v1.m[nodo.texto];
  }
  if (nodo.tipo == "[") {
    if (v1.kind != 2)
      rechazarruntime(nodo.linea, nodo.columna, "indexed access to a non-array.");
    tvalor v2 = ejecutaexpresion(nodo.hijo[1], in, out, valor, memoria, modelo);
    comprobarentero("array[...]", v2);
    if (v2.x < 0)
      rechazarruntime(nodo.linea, nodo.columna, "out of range in array access.");
    if (v1.format->texto != "") {
      if (int(v1.v.size()) <= v2.x)
        rechazarruntime(nodo.linea, nodo.columna, "out of range in array of fixed size access.");
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
      rechazarruntime(nodo.linea, nodo.columna, "back access to a non-array.");
    if (int(v1.v.size()) == 0)
      rechazarruntime(nodo.linea, nodo.columna, "back access to an array with 0 size.");
    return v1.v.back();
  }
  //nodo.tipo=="push":
  if (v1.kind != 2)
    rechazarruntime(nodo.linea, nodo.columna, "push action on a non-array.");
  if (v1.format->texto != "")
    rechazarruntime(nodo.linea, nodo.columna, "push to array of fixed size.");
  tvalor defecto;
  valorpordefecto(v1.format->hijo[0], defecto);
  memoria += 1 + computausomemoria(defecto);
  controlmemoria(memoria);
  v1.v.push_back(defecto);
  return v1.v.back();
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
                        prefijo + (prefijo == "" ? "" : ".") + valor.format->listacampos()[i], lineas))
        return 1;
  } else if (valor.kind == 2) {
    if (valor.format->hijo[0].tipo == "int" or
        valor.format->hijo[0].tipo == "string") {
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

void generamuestra(tvalor &valor, string &muestra)
{
  int lineas = 0;
  generamuestra(valor, muestra, "", lineas);
}

void generamuestra(vector<tvalor> &v, vector<string> &muestra)
{
  muestra = vector<string> (int(v.size()), "");
  for (int i = 0; i < int(v.size()); i++) generamuestra(v[i], muestra[i]);
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

void comprobartipovariablelogica(tnodo& nodo, tvalor &out, tvalor &variablelogica)
{
  if (MODE != reduc)
    rechazarruntime(nodo.linea, nodo.columna, "logical formulas can only appear in a reduction to SAT");

  if (out.format->tipo != "array" or out.format->texto != "" or
      out.format->hijo[0].tipo != "array" or out.format->hijo[0].texto != "" or
      out.format->hijo[0].hijo[0].tipo != "string")
    rechazar("Internal error: the output of the reduction does not have the expected format \"array of array of string\"");

  if (variablelogica.kind != 1)
    rechazarruntime(nodo.linea, nodo.columna, "stand alone expressions must be logical formulas.");
}

const int infinito = 1000000000;
const int finito = 100000;
int tiempoejecucion;

// El resultado de la ejecucion==0 significa que no ha terminado, ==1 que se ha terminado con normalidad.
int ejecutainstruccion(tnodo &nodo, tvalor &in, tvalor &out, map<string, tvalor> &valor, int &memoria,
            sat_solver const *modelo)
{
  tiempoejecucion--;
  if (tiempoejecucion < 0)
    rechazar("Runtime error: the execution time of the reduction is too big.");
  if (nodo.tipo == ";") {
  } else if (nodo.tipo=="and" or nodo.tipo=="or" or nodo.tipo=="atmost" or nodo.tipo=="atleast" or
      nodo.tipo=="exactly" or nodo.tipo=="not" or nodo.tipo=="implies" or nodo.tipo=="iff" or
      nodo.tipo=="string" or nodo.tipo=="stringparametrizado" or nodo.tipo=="identificador") {
    if (MODE == reduc) {
      int lenoutini = int(out.v.size());
      tvalor variablelogica = ejecutaexpresion(nodo, in, out, valor, memoria, modelo);
      comprobartipovariablelogica(nodo, out, variablelogica);
      out.v.push_back(tvalor(0, tvalor(variablelogica.s)));
      if (storestringformula) out.stringformula += variablelogica.stringformula+"\n";
      tnodo* formatarray = &(out.format->hijo[0]);
      tnodo* formatstring = &(out.format->hijo[0].hijo[0]);
      for (int i = lenoutini; i < int(out.v.size()); i++) {
        memoria += 1 + computausomemoria(out.v[i]);
        tvalor &valoraux = out.v[i];
        valoraux.format = formatarray;
        for (int j = 0; j < int(valoraux.v.size()); j++)
          valoraux.v[j].format = formatstring;
      }
      controlmemoria(memoria);
    } else {
      rechazarruntime(nodo.linea, nodo.columna, "stand-alone logical formulas can only appear in the reduction.");
    }
  } else if (nodo.tipo == "push") {
    extraerout(nodo, in, out, valor, memoria, modelo);
  } else if (nodo.tipo == "if") {
    tvalor r = ejecutaexpresion(nodo.hijo[0], in, out, valor, memoria, modelo);
    comprobarentero("if (...)", r);
    if (r.x) {
      int e = ejecutainstruccion(nodo.hijo[1], in, out, valor, memoria, modelo);
      if (e) return e;
    } else if (int(nodo.hijo.size()) == 3) {
      int e = ejecutainstruccion(nodo.hijo[2], in, out, valor, memoria, modelo);
      if (e) return e;
    }
  } else if (nodo.tipo == "while") {
    for (;;) {
      tvalor r = ejecutaexpresion(nodo.hijo[0], in, out, valor, memoria, modelo);
      comprobarentero("while (...)", r);
      if (not r.x) break;
      int e = ejecutainstruccion(nodo.hijo[1], in, out, valor, memoria, modelo);
      if (e) return e;
    }
  } else if (nodo.tipo == "foreach") {
    if (nodo.hijo[1].tipo == "..") { //foreach sobre rango
      //hijos: 0: variable, 1: rango, 2: instruccion
      tvalor rango1 = ejecutaexpresion(nodo.hijo[1].hijo[0], in, out, valor, memoria, modelo);
      comprobarentero(" .. ", rango1);
      tvalor rango2 = ejecutaexpresion(nodo.hijo[1].hijo[1], in, out, valor, memoria, modelo);
      comprobarentero(" .. ", rango2);
      for (int i = rango1.x; i <= rango2.x; i++) {
        valor[nodo.hijo[0].texto].kind = 0;
        valor[nodo.hijo[0].texto].x = i;
        int e = ejecutainstruccion(nodo.hijo[2], in, out, valor, memoria, modelo);
        if (e) return e;
      }
    }
    else { //foreach sobre array
      //hijos: 0: indice (opcional), 1: variable, 2: array, 3: instruccion
      int indicereferencia = (nodo.hijo.size() == 3 ? 0 : 1);
      tvalor &v2 = extraerelemento(nodo.hijo[indicereferencia + 1], in, out, valor, memoria, modelo);
      if (v2.kind != 2)
        rechazarruntime(nodo.linea, nodo.columna, "for-in requires a reference to the input being an array.");
      for (int i = 0; i < int(v2.v.size()); i++) {
        if (indicereferencia) {
          valor[nodo.hijo[0].texto].kind = 0;
          valor[nodo.hijo[0].texto].x = i;
        }
        valor[nodo.hijo[indicereferencia].texto].kind = 3;
        valor[nodo.hijo[indicereferencia].texto].ref = &v2.v[i];
        int e = ejecutainstruccion(nodo.hijo[indicereferencia + 2], in, out, valor, memoria, modelo);
        if (e) return e;
      }
    }
  } else if (nodo.tipo == "for") {
    int e = ejecutainstruccion(nodo.hijo[0], in, out, valor, memoria, modelo);
    if (e) return e;
    for (;;) {
      tvalor r = ejecutaexpresion(nodo.hijo[1], in, out, valor, memoria, modelo);
      comprobarentero("for (;...;)", r);
      if (not r.x) break;
      int e;
      e = ejecutainstruccion(nodo.hijo[3], in, out, valor, memoria, modelo);
      if (e) return e;
      e = ejecutainstruccion(nodo.hijo[2], in, out, valor, memoria, modelo);
      if (e) return e;
    }
  } else if (nodo.tipo == "++") {
    tvalor valorid = ejecutaexpresion(nodo.hijo[0], in, out, valor, memoria, modelo);
    comprobarentero("++", valorid);
    valor[nodo.hijo[0].texto].x++;
  } else if (nodo.tipo == "--") {
    tvalor valorid = ejecutaexpresion(nodo.hijo[0], in, out, valor, memoria, modelo);
    comprobarentero("--", valorid);
    valor[nodo.hijo[0].texto].x--;
  } else if (nodo.tipo == "=") {
    tvalor v2 = ejecutaexpresion(nodo.hijo[1], in, out, valor, memoria, modelo);
    //if (nodo.hijo[0].tipo=="identificador")
    // Haria falta aqui comprobar que lo que se asigna es de tipo entero o string?
    valor[nodo.hijo[0].texto] = v2;
  } else if (nodo.tipo == "&=") {
    tvalor &v2 = extraerelemento(nodo.hijo[1], in, out, valor, memoria, modelo);
    valor[nodo.hijo[0].texto].kind = 3;
    valor[nodo.hijo[0].texto].ref = &v2;
  } else if (nodo.tipo == "=,") {
    tvalor &v1 = extraerout(nodo.hijo[0], in, out, valor, memoria, modelo);
    memoria -= computausomemoria(v1);

    if (int(nodo.hijo.size()) == 2) {
      tvalor v2 = ejecutaexpresion(nodo.hijo[1], in, out, valor, memoria, modelo);
      // Haria falta aqui comprobar que lo que se asigna es de tipo entero o string?
      if (v1.format->tipo == "int") {
        if (v2.kind != 0)
          rechazarruntime(nodo.linea, nodo.columna, "incompatible types in assignment.\nAn \"int\" was expected.");
        // No se copia v1=v2 para mantener "tnodo *format;" de v1.
        v1.kind = v2.kind;
        v1.x = v2.x;
        v1.s = v2.s;
      } else if (v1.format->tipo == "string") {
        // Este error creo que no deberia tener lugar nunca porque el ejecuta expresion siempre da int o string.
        if (v2.kind != 0 and v2.kind != 1)
          rechazarruntime(nodo.linea, nodo.columna, "incompatible types in assignment.\nAn \"int\" or \"string\" was expected.");
        // No se copia v1=v2 para mantener "tnodo *format;" de v1.
        v1.kind = v2.kind;
        v1.x = v2.x;
        v1.s = v2.s;
      } else
        rechazarruntime(nodo.linea, nodo.columna, "incompatible types in assignment.\nOnly simple types can be assigned.");
    } else if (v1.kind == 2) {
      if (v1.format->hijo[0].tipo != "int" and v1.format->hijo[0].tipo != "string")
        rechazarruntime(nodo.linea, nodo.columna, "only simple types can be assigned,\nand the positions of the array do not have simple types.");
      if (v1.format->texto != "") {
        int tamanyo = stoll(v1.format->texto);
        if (tamanyo != int(nodo.hijo.size()) - 1)
          rechazarruntime(nodo.linea, nodo.columna, "the number of expressions does not coincide with the fixed size of the array.");
      } else {
        tvalor defecto;
        valorpordefecto(v1.format->hijo[0], defecto);
        v1.v = vector<tvalor> (int(nodo.hijo.size()) - 1, defecto);
      }
      for (int i = 1; i < int(nodo.hijo.size()); i++) {
        tvalor v2 = ejecutaexpresion(nodo.hijo[i], in, out, valor, memoria, modelo);
        if (v1.format->hijo[0].tipo == "int" and v2.kind != 0)
          rechazarruntime(nodo.linea, nodo.columna, "incompatible types in assignment.\nAn \"int\" was expected in the expresion number " + itos(i) + ".");
        v1.v[i - 1].kind = v2.kind;
        v1.v[i - 1].x = v2.x;
        v1.v[i - 1].s = v2.s;
      }
    } else if (v1.kind == 4) {
      if (int(nodo.hijo.size()) - 1 != int(v1.format->m.size()))
        rechazarruntime(nodo.linea, nodo.columna, "the number of expressions does not coincide with the number of fields in the struct.");
      for (int i = 1; i < int(nodo.hijo.size()); i++) {
        tvalor v2 = ejecutaexpresion(nodo.hijo[i], in, out, valor, memoria, modelo);
        if (v1.format->m[v1.format->listacampos()[i - 1]].tipo == "int" and v2.kind != 0)
          rechazarruntime(nodo.linea, nodo.columna, "incompatible types in assignment.\nAn \"int\" was expected in the expresion number " + itos(i) + ".");
        if (v1.format->m[v1.format->listacampos()[i - 1]].tipo != "int" and
            v1.format->m[v1.format->listacampos()[i - 1]].tipo != "string")
          rechazarruntime(nodo.linea, nodo.columna, "incompatible types in assignment.\nThe field number " + itos(i) + " of the struct is not \"int\" or \"string\".");
        v1.m[v1.format->listacampos()[i - 1]].kind = v2.kind;
        v1.m[v1.format->listacampos()[i - 1]].x = v2.x;
        v1.m[v1.format->listacampos()[i - 1]].s = v2.s;
      }
    } else
      rechazarruntime(nodo.linea, nodo.columna, "incompatible types in assignment.\nOnly simple types can be assigned.");
    memoria += computausomemoria(v1);
    controlmemoria(memoria);
  } else if (nodo.tipo == "stop") {
    return 1;
  } else if (nodo.tipo == "lista") {
    for (int i = 0; i < int(nodo.hijo.size()); i++)
      if (ejecutainstruccion(nodo.hijo[i], in, out, valor, memoria, modelo))
        return 1;
  } else
    rechazarruntime(nodo.linea, nodo.columna, "unknown instruction \"" + nodo.tipo + "\".");
  return 0;
}

void ejecuta(tnodo &nodo, tvalor &in, tvalor &out,
             sat_solver const *modelo = NULL)
{
  numid = 1;
  map<string, tvalor> valor;
  int memoria = computausomemoria(out);

  ejecutainstruccion(nodo.hijo[0], in, out, valor, memoria, modelo);
}

vector<string> breaklines(const string& s) {
  vector<string> res(1, "");
  for (uint i = 0; i < s.size(); i++) {
    if (s[i] == '\n') res.push_back("");
    else res.back() += s[i];
  }
  return res;
}

void ejecuta(tnodo &nodo, vector<tvalor> &vin, vector<tvalor> &vout, tnodo &formatout,
             string mensajeprefijoerror, Modo modo, vector<vector<string> > *historialesinsertsat = NULL)
{
  prefijoerror = mensajeprefijoerror;
  MODE = modo;
  int tiempoejecucionini = (MODE == inter) ? infinito : finito;
  if (historialesinsertsat != NULL) {
    *historialesinsertsat = vector<vector<string> >(int(vin.size()), vector<string>());
  }

  tvalor defecto;
  valorpordefecto(formatout, defecto);
  vout = vector<tvalor> (int(vin.size()), defecto);

  for (int i = 0; i < int(vin.size()); i++) {
    tiempoejecucion = tiempoejecucionini;
    if (historialesinsertsat != NULL) storestringformula = true;
    ejecuta(nodo, vin[i], vout[i]);
    storestringformula = false;
    if (historialesinsertsat != NULL)
      (*historialesinsertsat)[i] = breaklines(vout[i].stringformula);
  }
}

void ejecutareconstruccion(tnodo &reconstructor, tvalor &in, tnodo &formatout, sat_solver const *modelo, string &muestrasolucion,
                           string &ficherovalidador, tnodo &validador, tnodo &formatvalidador, tvalor &validado)
{

  MODE = recon;
  prefijoerror = "";
  tiempoejecucion = infinito;

  tvalor out;
  valorpordefecto(formatout, out);
  tiempoejecucion = infinito;
  ejecuta(reconstructor, in, out, modelo);
  generamuestra(out, muestrasolucion);

  MODE = inter;
  prefijoerror = "Internal error running: " + ficherovalidador + "\n";
  tiempoejecucion = infinito;

  tvalor jpysolucion;
  tnodo nodojpysolucion;
  construirstruct("input", in, "solution", out, nodojpysolucion, jpysolucion);
  valorpordefecto(formatvalidador, validado);
  ejecuta(validador, jpysolucion, validado);
  prefijoerror = "";
}

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Errores genericos:

void errorprogramademasiadogrande()
{
  rechazar("Error: the program is too big. Please, find a simpler solution");
}

void errorcosasdespuesdelprograma(int linea, int columna)
{
  rechazar(linea, columna, "there should not be anything else just after the program.");
}

void errorrespuesta(string respuesta, string &in, string &out)
{
  rechazar("Error: the " + respuesta + " answer is not preserved when your reduction\n" +
        "receives the following input:\n\n" + in + "\nThe corresponding obtained output is:\n\n" + out +
        "\nIf you consider that the judge verdict is not correct,\n" +
        "try to submit a simpler reduction in order to ease the testing process.");
}

void errorrespuesta2SAT(string respuesta, string &in, string &out,
                        string muestrasolucion = "", string muestra = "")
{
  bool mostrarmuestra = not muestrasolucion.empty() or not muestra.empty();
  rechazar("Error: the " + respuesta + " answer is not preserved when your reduction to SAT\n" +
        "receives the following input:\n\n" + in + "\nThe corresponding generated formula is:\n\n" + out +
        (mostrarmuestra ? "\nThe corresponding reconstructed solution is:\n\n" + muestrasolucion + "\n" + muestra + "\n" : string()) +
        "\nIf you consider that the judge verdict is not correct,\n" +
        "try to submit a simpler reduction in order to ease the testing process.");
}

void errorreconstruccion(string mesaje, string &in, string &out)
{
  rechazar("Error: the reduction is apparently correct, but the reconstructed solution is\n"
        "wrong when your programs receive the following input:\n\n" + in + "\nThe corresponding reconstructed solution is:\n\n" + out +
        (not mesaje.empty() ? "\n" + mesaje + "\n" : string()));
}

void mensajeaceptacionconreconstruccion()
{
  morirpuro("accepted", "Reduction and solution reconstruction apparently correct.");
}

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Analisis lexico del formateador (analizador de tipo):

set<string> palabrasclaveformat = {"struct", "array", "int", "string", "of"};
set<string> cadenasclaveformat = {"{", "}", "[", "]", ":", "//"};

void leerentradaformat(string &s, vector<ttoken> &vt, int linea)
{
  int is = 0;
  saltarblancos(s, is);
  while (is < int(s.size())) {
    leertoken(s, is, vt, linea, 0, palabrasclaveformat, cadenasclaveformat);
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
      if (ivt == int(vt.size()) or vt[ivt].tipo != "constant")
        seesperabaver(vt, ivt, "\"constant\"");
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
  prefijoerror = "Internal error reading format: " + stringformat + "\n";
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
  prefijoerror = "Internal error reading format: " + ficheroformat + "\n";
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
  for (int i = 0; i < int(vvs.size()); i++) {
    v[i].kind=4;
    v[i].format=&format;
    leerjp(vvs[i], v[i].m[jpstring], format.m[jpstring]);
  }
}

void escribirtnodo(tnodo &nodo,int identacion)
{
  cout<<string(identacion,' ')<<nodo.tipo;
  if (nodo.texto!="") cout<<"("<<nodo.texto<<")";
  cout<<endl;
  for (int i=0;i<int(nodo.hijo.size());i++)
    escribirtnodo(nodo.hijo[i],identacion+2);
}

void escribirtnodo(string nombreprograma, tnodo &nodo)
{
  cout << "======================" << endl;
  cout << "Analisis sintactico " << nombreprograma << endl;
  cout << "======================" << endl;
  escribirtnodo(nodo,0);
  cout << endl << endl;
}

void escribirtokens(string nombreprograma, vector<ttoken>& vt) {
  cout << "======================" << endl;
  cout << "Analisis lexico " << nombreprograma << endl;
  cout << "======================" << endl;
  for (int i=0;i<int(vt.size());i++) {
    cout<<i<<":\t"<<vt[i].tipo;
    if (vt[i].texto != "") {
      cout << "(" << vt[i].texto << ")";
    }
    cout <<"\t["<<vt[i].linea<<", "<<vt[i].columna<<"]" << endl;
  }
  cout<<endl<<endl;
}


void leerprograma(string ficheroprograma, tnodo &nodo, string tipoprograma, const vector<string>& infields, const vector<string>& outfields)
{
  prefijoerror = "Internal error reading program: " + ficheroprograma + "\n";

  vector<string> vs = leerfichero(ficheroprograma);
  vector<ttoken> vt;
  leerentrada(vs, vt, infields, outfields);
  if (int(vt.size()) > limitenumtokens)
    errorprogramademasiadogrande();

  if (DBG_MODE) escribirtokens(ficheroprograma, vt);

  int ivt = 0;
  parsing(nodo, vt, ivt, tipoprograma);
  if (ivt < int(vt.size()))
    errorcosasdespuesdelprograma(vt[ivt].linea, vt[ivt].columna);

  if (DBG_MODE) escribirtnodo(ficheroprograma, nodo);
}

void leerpropuestasolucion(string ficheroprograma, tnodo &nodo1, tnodo &nodo2,
  const vector<string>& formatinput, const vector<string>& formatsolucion)
{
  prefijoerror = "";
  vector<string> vs = leerfichero(ficheroprograma);
  vector<ttoken> vt;
  leerentrada(vs, vt, formatinput, formatsolucion);
  if (int(vt.size()) > limitenumtokens)
    errorprogramademasiadogrande();

  if (DBG_MODE) escribirtokens(ficheroprograma, vt);

  int ivt = 0;
  parsing(nodo1, vt, ivt, "reduction");
  parsing(nodo2, vt, ivt, "reconstruction");
  if (ivt < int(vt.size()))
    errorcosasdespuesdelprograma(vt[ivt].linea, vt[ivt].columna);

  if (DBG_MODE) escribirtnodo("propuestasolucionreduccion", nodo1);
  if (DBG_MODE) escribirtnodo("propuestasolucionreconstruccion", nodo2);
}

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
// Programa principal:

string sformatjp = "struct { "+jpstring+" : array of array of int }";
string sformatsat = "array of array of string";
string sformatvalidador = "struct { valid : int msg : string }";

vector<string> getfieldsstruct(tnodo& nodo) {
  if (nodo.tipo != "struct") {
    prefijoerror = "";
    rechazar("Internal error: node is not a struct");
  }
  vector<string> res;
  for (string f : nodo.listacampos()) {
    res.push_back(f);
  }
  return res;
}

int main(int argc, char *argv[])
{

  for (int i = 1; i < argc; i++) {
    if (string(argv[i]) == "-d") DBG_MODE = true;
    if (DBG_MODE and i < argc-1) argv[i] = argv[i+1]; //shift arguments to their normal position
  }

  if (argc != (DBG_MODE ? 8 : 7))
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
  leerprograma(ficherojp2input, nodojp2input, "main", getfieldsstruct(formatjp), getfieldsstruct(formatinput));
  leerprograma(ficheroinput2sat, nodoinput2sat, "reduction", getfieldsstruct(formatinput), vector<string> (0));
  leerprograma(ficherovalidador, nodovalidador, "main", {"input", "solution"}, getfieldsstruct(formatvalidador));
  leerpropuestasolucion(ficheropropuestasolucion, nodopropuestasolucion2sat, nodopropuestasolucion2solucion,
    getfieldsstruct(formatinput), getfieldsstruct(formatsolucion));

  comprobarnoseusatipo(nodopropuestasolucion2sat, "outprefix",
                       "the output cannot be directly accessed in a reduction to SAT,\nuse logical expressions directly to create your formula.");

  cout << "TIEMPO LECTURA Y PARSING = " << (OUTPUT_RUNTIMES ? tlectura.elapsedstring() : "-1") << endl;

  timer tejecucion1a;
  vector<tvalor> vinput, vsat1, vsat2;
  vector<string> muestrainput, muestraoutput;
  ejecuta(nodojp2input, vjp, vinput, formatinput,
    "Internal error running jp2input: " + ficherojp2input + "\n", inter);
  generamuestra(vinput, muestrainput);
  ejecuta(nodoinput2sat, vinput, vsat1, formatsat,
    "Internal error running input2sat: " + ficheroinput2sat + "\n", reduc);
  vector<vector<string> > historialesinsertsat;
  timer tejecucion1b;
  ejecuta(nodopropuestasolucion2sat, vinput, vsat2, formatsat, "", reduc, &historialesinsertsat);
  if (DBG_MODE) {
    cout << "====== historiales insertsat ======" << endl;
    for (uint i = 0; i < historialesinsertsat.size(); i++) {
      cout << ">>>> " << i << ":" << endl;
      for (uint j = 0; j < historialesinsertsat[i].size(); j++) {
        cout << historialesinsertsat[i][j] << endl;
      }
    }
  }
  generamuestra(historialesinsertsat, muestraoutput, "");
  cout << "TIEMPO EJECUCION (to sat) = " << (OUTPUT_RUNTIMES ? tejecucion1a.elapsedstring() : "-1")
       << " (" << (OUTPUT_RUNTIMES ? tejecucion1b.elapsedstring() : "-1")
      << " en propuestasolucion)" << endl;
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
    if (DBG_MODE and respuestaout) {
      cout << "======================" << endl;
      cout << "modelo SAT: " << i << endl;
      cout << "======================" << endl;
      S2[i].printmodelo();
    }
    segaccum += segresolverin + segresolverout;
    if (not OUTPUT_RUNTIMES) segaccum = segresolverout = segresolverin = -1;
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
        errorrespuesta2SAT("positive", muestrainput[i], muestraoutput[i]);
      if (not respuestain and respuestaout) {
        string muestrasolucion;
        tvalor validado;
        ejecutareconstruccion(nodopropuestasolucion2solucion, vinput[i], formatsolucion, &S2[i], muestrasolucion,
                              ficherovalidador, nodovalidador, formatvalidador, validado);
        errorrespuesta2SAT("negative", muestrainput[i], muestraoutput[i],
                           muestrasolucion, validado.m["msg"].s);
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
      errorreconstruccion(validado.m["msg"].s, muestrainput[i], muestrasolucion);
  }
  cout << "TIEMPO EJECUCION (reconstruccion, validacion) = " << (OUTPUT_RUNTIMES ? tejecucion2.elapsedstring() : "-1") << endl;
  for (int j = 0; j < int(vjp.size()); ++j)
    cout << infoextensa[j].str();
  prefijoerror = "";
  mensajeaceptacionconreconstruccion();
}
