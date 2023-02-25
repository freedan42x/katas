#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <stdio.h>

typedef enum
{
  LIT         = 0x01,
  NEGATE      = 0x02,
  PLUS        = 0x04,
  MINUS       = 0x08,
  MULT        = 0x10,
  DIV         = 0x20,
  OPEN_PAREN  = 0x40,
  CLOSE_PAREN = 0x80
} TokenType;

typedef struct
{
  TokenType type;
  double lit;
} Token;

void trim(const char **s)
{
  while (**s == ' ') (*s)++;
}

bool chop_lit(const char **s, Token *t)
{
  char buf[32];
  size_t buf_len = 0;
  while (isdigit(**s) || **s == '.') {
    buf[buf_len++] = **s;
    (*s)++;
  }

  if (!buf_len) return false;
  
  buf[buf_len] = 0;
  *t = (Token) {LIT, atof(buf)};
  return true;
}

bool chop_op(const char **s, Token *t)
{
  switch (**s) {
  case '+': return *t = (Token) {PLUS}, (*s)++, true;
  case '-': return *t = (Token) {MINUS}, (*s)++, true;
  case '*': return *t = (Token) {MULT}, (*s)++, true;
  case '/': return *t = (Token) {DIV}, (*s)++, true;
  } 

  return false;
}

bool chop_paren(const char **s, Token *t)
{
  switch (**s) {
  case '(': return *t = (Token) {OPEN_PAREN}, (*s)++, true;
  case ')': return *t = (Token) {CLOSE_PAREN}, (*s)++, true;
  } 

  return false; 
}

#define TOKENS_INITIAL_CAP 256
typedef struct
{
  Token *tokens;
  size_t tokens_len;
  size_t tokens_cap;
} Tokens;

Tokens *tokens_make(void)
{
  Tokens *ts = malloc(sizeof(Tokens));
  ts->tokens_cap = TOKENS_INITIAL_CAP;
  ts->tokens_len = 0;
  ts->tokens = malloc(sizeof(Token) * ts->tokens_cap);

  return ts;
}

Tokens *tokens_slice(Tokens *ts, size_t begin, size_t len)
{
  assert(begin + len <= ts->tokens_len);

  Tokens *ts_copy = malloc(sizeof(Tokens));
  ts_copy->tokens_cap = ts->tokens_cap;
  ts_copy->tokens_len = len;
  ts_copy->tokens = malloc(sizeof(Token) * ts_copy->tokens_cap);
  memcpy(ts_copy->tokens, &ts->tokens[begin], sizeof(Token) * len);

  return ts_copy;
}

void tokens_free(Tokens *ts)
{
  free(ts->tokens);
  free(ts);
}

void tokens_put(Tokens *ts, Token t)
{
  if (ts->tokens_len >= ts->tokens_cap) {
    ts->tokens_cap *= 2;
    ts->tokens = realloc(ts->tokens, sizeof(Token) * ts->tokens_cap);
  }

  ts->tokens[ts->tokens_len++] = t;
}

Tokens *tokens_parse(const char *s)
{
  Tokens *ts = tokens_make();
  bool prev_lit = false;
  while (*s) {
    trim(&s);

    Token t;
    while (chop_paren(&s, &t)) {
      tokens_put(ts, t);
      trim(&s);
    };

    if (*s == '-') {
      if (prev_lit) {
	      tokens_put(ts, (Token) {MINUS});
	      prev_lit = false;
      } else {
       	tokens_put(ts, (Token) {NEGATE});
      }
      s++;
    }

    if (chop_lit(&s, &t)) {
      prev_lit = true;
      tokens_put(ts, t);
    }

    if (chop_op(&s, &t)) {
      prev_lit = false;
      tokens_put(ts, t);
    }
  }

  return ts;
}

void tokens_subst(Tokens *ts, Token t, size_t begin, size_t len)
{
  assert(ts->tokens_len >= begin + len);
  
  memmove(&ts->tokens[begin + 1],
	  &ts->tokens[begin + len],
	  sizeof(Token) * (ts->tokens_len - begin - len));
  ts->tokens[begin] = t;
  ts->tokens_len = ts->tokens_len - len + 1;
}

bool tokens_find(Tokens *ts, int mask, size_t *out_ix)
{
  for (size_t i = 0; i < ts->tokens_len; i++) {
    if (ts->tokens[i].type & mask) {
      *out_ix = i;
      return true;
    }
  }

  return false;
}

bool tokens_find_deepest_paren(Tokens *ts, size_t *out_begin, size_t *out_len)
{
  size_t open = 0;
  size_t open_max = 0;
  size_t open_ix = -1;
  size_t open_max_ix = -1;
  size_t close_max_ix = -1;
  for (size_t i = 0; i < ts->tokens_len; i++) {
    if (ts->tokens[i].type == OPEN_PAREN) {
      open++;
      open_ix = i;
    } else if (ts->tokens[i].type == CLOSE_PAREN) {
      if (open > open_max) {
	      open_max = open;
	      open_max_ix = open_ix;
	      close_max_ix = i;
      }
      open--;
    }
  }

  if (open_max_ix == -1) return false;

  *out_begin = open_max_ix;
  *out_len = close_max_ix - open_max_ix + 1;
  return true;
}

double apply_bin_op(TokenType type, double x, double y)
{
  if (type == PLUS) return x + y;
  if (type == MINUS) return x - y;
  if (type == MULT) return x * y;
  if (type == DIV) return x / y;
  assert(0 && "not a binary operation");
}

Token tokens_eval_noparens(Tokens *ts)
{
  size_t k;
  if (tokens_find(ts, NEGATE, &k)) {
    assert(k + 1 < ts->tokens_len && "expected something to negate");
    Token t = ts->tokens[k + 1];
    assert(t.type == LIT && "should negate only LIT; all parentheses should be evaluated before NEGATE");
    t.lit *= -1;
    tokens_subst(ts, t, k, 2);
    return tokens_eval_noparens(ts);
  }

  if (tokens_find(ts, MULT | DIV, &k)) {
    assert(k - 1 >= 0 && ts->tokens[k - 1].type == LIT && "lhs should be LIT");
    assert(k + 1 < ts->tokens_len && ts->tokens[k + 1].type == LIT && "rhs should be LIT");
    double r = apply_bin_op(ts->tokens[k].type, ts->tokens[k - 1].lit, ts->tokens[k + 1].lit);
    tokens_subst(ts, (Token) {LIT, r}, k - 1, 3);
    return tokens_eval_noparens(ts);
  }

  if (tokens_find(ts, PLUS | MINUS, &k)) {
    assert(k - 1 >= 0 && ts->tokens[k - 1].type == LIT && "lhs should be LIT");
    assert(k + 1 < ts->tokens_len && ts->tokens[k + 1].type == LIT && "rhs should be LIT");
    double r = apply_bin_op(ts->tokens[k].type, ts->tokens[k - 1].lit, ts->tokens[k + 1].lit);
    tokens_subst(ts, (Token) {LIT, r}, k - 1, 3);
    return tokens_eval_noparens(ts);
  }

  assert(ts->tokens_len == 1 && ts->tokens[0].type == LIT && "at this point only one single LIT is left");
  return ts->tokens[0];
}

double tokens_eval(Tokens *ts)
{
  size_t begin, len;
  if (tokens_find_deepest_paren(ts, &begin, &len)) {
    Tokens *slice = tokens_slice(ts, begin + 1, len - 2);
    Token t = tokens_eval_noparens(slice);
    tokens_free(slice);
    tokens_subst(ts, t, begin, len);
    return tokens_eval(ts);
  }

  return tokens_eval_noparens(ts).lit;
}

double calculate(const char *expr)
{
  Tokens *ts = tokens_parse(expr);
  double r = tokens_eval(ts);
  tokens_free(ts);
  return r;
}
