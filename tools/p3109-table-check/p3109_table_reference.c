#include <stdbool.h>
#include <stdio.h>

typedef struct {
  const char *name;
  int precision;
  bool is_signed;
  bool is_extended;
} format;

static const format formats[] = {
    {"Binary4p1se", 1, true, true},
    {"Binary4p2se", 2, true, true},
    {"Binary4p3se", 3, true, true},
    {"Binary4p1sf", 1, true, false},
    {"Binary4p2sf", 2, true, false},
    {"Binary4p3sf", 3, true, false},
    {"Binary4p1ue", 1, false, true},
    {"Binary4p2ue", 2, false, true},
    {"Binary4p3ue", 3, false, true},
    {"Binary4p4ue", 4, false, true},
    {"Binary4p1uf", 1, false, false},
    {"Binary4p2uf", 2, false, false},
    {"Binary4p3uf", 3, false, false},
    {"Binary4p4uf", 4, false, false},
};

static void decode_token(const format *f, int code, char token[32]) {
  const int sign_base = 8;
  const int max_code = 15;
  const int trailing_modulus = 1 << (f->precision - 1);
  const int bias = f->is_signed ? 1 << (4 - f->precision - 1)
                                : 1 << (4 - f->precision);

  if ((f->is_signed && code == sign_base) ||
      (!f->is_signed && code == max_code)) {
    (void)snprintf(token, 32, "nan");
    return;
  }
  if (f->is_extended &&
      ((f->is_signed && code == sign_base - 1) ||
       (!f->is_signed && code == max_code - 1))) {
    (void)snprintf(token, 32, "+inf");
    return;
  }
  if (f->is_signed && f->is_extended && code == max_code) {
    (void)snprintf(token, 32, "-inf");
    return;
  }

  const bool negative = f->is_signed && code > sign_base;
  const int magnitude_code = negative ? code - sign_base : code;
  const int exponent_field = magnitude_code / trailing_modulus;
  const int trailing_field = magnitude_code % trailing_modulus;
  int significand;
  int exponent;

  if (exponent_field == 0) {
    significand = trailing_field;
    exponent = 2 - bias - f->precision;
  } else {
    significand = trailing_modulus + trailing_field;
    exponent = exponent_field - bias - f->precision + 1;
  }

  if (significand == 0) {
    (void)snprintf(token, 32, "zero");
  } else {
    if (negative) {
      significand = -significand;
    }
    (void)snprintf(token, 32, "finite:%d:%d", significand, exponent);
  }
}

int main(void) {
  const size_t format_count = sizeof(formats) / sizeof(formats[0]);
  for (size_t i = 0; i < format_count; ++i) {
    printf("%s", formats[i].name);
    for (int code = 0; code < 16; ++code) {
      char token[32];
      decode_token(&formats[i], code, token);
      printf(" %s", token);
    }
    putchar('\n');
  }
  return 0;
}
