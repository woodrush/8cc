// Copyright 2012 Rui Ueyama. Released under the MIT license.

#include <stddef.h>
#include "test.h"

static void t1() {
    struct { int a; } x;
    x.a = 61;
    expect(61, x.a);
}

static void t2() {
    struct { int a; int b; } x;
    x.a = 61;
    x.b = 2;
    expect(63, x.a + x.b);
}

static void t3() {
    struct { int a; struct { char b; int c; } y; } x;
    x.a = 61;
    x.y.b = 3;
    x.y.c = 3;
    expect(67, x.a + x.y.b + x.y.c);
}

static void t4() {
    struct tag4 { int a; struct { char b; int c; } y; } x;
    struct tag4 s;
    s.a = 61;
    s.y.b = 3;
    s.y.c = 3;
    expect(67, s.a + s.y.b + s.y.c);
}

static void t5() {
    struct tag5 { int a; } x;
    struct tag5 *p = &x;
    x.a = 68;
    expect(68, (*p).a);
}

static void t6() {
    struct tag6 { int a; } x;
    struct tag6 *p = &x;
    (*p).a = 69;
    expect(69, x.a);
}

static void t7() {
    struct tag7 { int a; int b; } x;
    struct tag7 *p = &x;
    x.b = 71;
    expect(71, (*p).b);
}

static void t8() {
    struct tag8 { int a; int b; } x;
    struct tag8 *p = &x;
    (*p).b = 72;
    expect(72, x.b);
}

static void t9() {
    struct tag9 { int a[3]; int b[3]; } x;
    x.a[0] = 73;
    expect(73, x.a[0]);
    x.b[1] = 74;
    expect(74, x.b[1]);
    expect(74, x.a[4]);
}

struct tag10 {
    int a;
    struct tag10a {
        char b;
        int c;
    } y;
} v10;
static void t10() {
    v10.a = 71;
    v10.y.b = 3;
    v10.y.c = 3;
    expect(77, v10.a + v10.y.b + v10.y.c);
}

struct tag11 { int a; } v11;
static void t11() {
    struct tag11 *p = &v11;
    v11.a = 78;
    expect(78, (*p).a);
    expect(78, v11.a);
    expect(78, p->a);
    p->a = 79;
    expect(79, (*p).a);
    expect(79, v11.a);
    expect(79, p->a);
}

struct tag12 {
    int a;
    int b;
} x;
static void t12() {
    struct tag12 a[3];
    a[0].a = 83;
    expect(83, a[0].a);
    a[0].b = 84;
    expect(84, a[0].b);
    a[1].b = 85;
    expect(85, a[1].b);
    int *p = (int *)a;
    expect(85, p[3]);
}

static void t13() {
    struct { char c; } v = { 'a' };
    expect('a', v.c);
}

static void t14() {
    struct { int a[3]; } v = { { 1, 2, 3 } };
    expect(2, v.a[1]);
}

static void unnamed() {
    struct {
        union {
            struct { int x; int y; };
            struct { char c[8]; };
        };
    } v;
    v.x = 1;
    v.y = 7;
    expect(1, v.c[0]);
    expect(7, v.c[4]);
}

static void assign() {
    struct { int a, b, c; short d; char f; } v1, v2;
    v1.a = 3;
    v1.b = 5;
    v1.c = 7;
    v1.d = 9;
    v1.f = 11;
    v2 = v1;
    expect(3, v2.a);
    expect(5, v2.b);
    expect(7, v2.c);
    expect(9, v2.d);
    expect(11, v2.f);
}

static void arrow() {
    struct cell { int val; struct cell *next; };
    struct cell v1 = { 5, NULL };
    struct cell v2 = { 6, &v1 };
    struct cell v3 = { 7, &v2 };
    struct cell *p = &v3;
    expect(7, v3.val);
    expect(7, p->val);
    expect(6, p->next->val);
    expect(5, p->next->next->val);

    p->val = 10;
    p->next->val = 11;
    p->next->next->val = 12;
    expect(10, p->val);
    expect(11, p->next->val);
    expect(12, p->next->next->val);
}

static void address() {
    struct tag { int a; struct { int b; } y; } x = { 6, 7 };
    int *p1 = &x.a;
    int *p2 = &x.y.b;
    expect(6, *p1);
    expect(7, *p2);
    expect(6, *&x.a);
    expect(7, *&x.y.b);

    struct tag *xp = &x;
    int *p3 = &xp->a;
    int *p4 = &xp->y.b;
    expect(6, *p3);
    expect(7, *p4);
    expect(6, *&xp->a);
    expect(7, *&xp->y.b);
}

static void incomplete() {
    struct tag1;
    struct tag2 { struct tag1 *p; };
    struct tag1 { int x; };

    struct tag1 v1 = { 3 };
    struct tag2 v2 = { &v1 };
    expect(3, v2.p->x);
}

static void bitfield_basic() {
    union {
        int i;
        struct { int a:5; int b:5; };
    } x;
    x.i = 0;
    x.a = 10;
    x.b = 11;
    expect(10, x.a);
    expect(11, x.b);
    expect(362, x.i); // 11 << 5 + 10 == 362
}

static void bitfield_mix() {
    union {
        int i;
        struct { char a:5; int b:5; };
    } x;
    x.a = 10;
    x.b = 11;
    expect(10, x.a);
    expect(11, x.b);
    expect(362, x.i);
}

static void bitfield_union() {
    union { int a : 10; char b: 5; char c: 5; } x;
    x.a = 2;
    expect(2, x.a);
    expect(2, x.b);
    expect(2, x.c);
}

static void bitfield_unnamed() {
    union {
        int i;
        struct { char a:4; char b:4; char : 8; };
    } x = { 0 };
    x.i = 0;
    x.a = 2;
    x.b = 4;
    expect(2, x.a);
    expect(4, x.b);
    expect(66, x.i);

    union {
        int i;
        struct { char a:4; char :0; char b:4; };
    } y = { 0 };
    y.a = 2;
    y.b = 4;
    expect(2, y.a);
    expect(4, y.b);
    expect(1026, y.i);
}

struct { char a:4; char b:4; } inittest = { 2, 4 };

static void bitfield_initializer() {
    expect(2, inittest.a);
    expect(4, inittest.b);

    struct { char a:4; char b:4; } x = { 2, 4 };
    expect(2, x.a);
    expect(4, x.b);
}

static void test_offsetof() {
    struct tag10 { int a, b; };
    expect(0, offsetof(struct tag10, a));
    expect(4, offsetof(struct tag10, b));
    int x[offsetof(struct tag10, b)];
    expect(4, sizeof(x) / sizeof(x[0]));

    expect(4, offsetof(struct { char a; struct { int b; }; }, b));
    expect(6, offsetof(struct { char a[3]; int : 10; char c; }, c));
    expect(6, offsetof(struct { char a[3]; int : 16; char c; }, c));
    expect(7, offsetof(struct { char a[3]; int : 17; char c; }, c));
    expect(2, offsetof(struct { char : 7; int : 7; char a; }, a));
    expect(0, offsetof(struct { char : 0; char a; }, a));

    expect(1, _Alignof(struct { int : 32; }));
    expect(2, _Alignof(struct { int : 32; short x; }));
    expect(4, _Alignof(struct { int x; int : 32; }));
}

static void flexible_member() {
    struct { int a, b[]; } x;
    expect(4, sizeof(x));
    struct { int a, b[0]; } y;
    expect(4, sizeof(y));
    struct { int a[0]; } z;
    expect(0, sizeof(z));

#ifdef __8cc__ // BUG
    struct t { int a, b[]; };
    struct t x2 = { 1, 2, 3 };
    struct t x3 = { 1, 2, 3, 4, 5 };
    expect(2, x3.b[0]);
    expect(3, x3.b[1]);
    expect(4, x3.b[2]);
    expect(5, x3.b[3]);
#endif
}

static void empty_struct() {
    struct tag15 {};
    expect(0, sizeof(struct tag15));
    union tag16 {};
    expect(0, sizeof(union tag16));
}

struct abi_check_nest {
    int a;
    int b;
    int c;
};

struct abi_check {
    int x;
    int y;
    struct abi_check_nest z;
};

struct abi_check_small {
    int x;
};

static int struct_arg_func(struct abi_check s1, struct abi_check s2) {
  int r = s1.x + s1.y + s1.z.a + s1.z.b + s1.z.c;
  r -= s2.x + s2.y + s2.z.a + s2.z.b + s2.z.c;
  expect(1, s1.x);
  expect(2, s1.y);
  expect(3, s1.z.a);
  expect(4, s1.z.b);
  expect(5, s1.z.c);
  expect(6, s2.x);
  expect(7, s2.y);
  expect(8, s2.z.a);
  expect(9, s2.z.b);
  expect(10, s2.z.c);
  return r;
}

static void struct_call(void) {
    struct abi_check s1 = { 1, 2, 3, 4, 5 };
    struct abi_check s2 = { 6, 7, 8, 9, 10 };
    expect(-25, struct_arg_func(s1, s2));
}

static void struct_local(void) {
    struct abi_check s = { 1, 2, 3, 4, 5 };
    struct abi_check_nest sn = s.z;
    expect(3, sn.a);
    expect(4, sn.b);
    expect(5, sn.c);
}

struct abi_check g_s = { 10, 11, 12, 13, 14 };

static void struct_global(void) {
    struct abi_check_nest sn = g_s.z;
    expect(12, sn.a);
    expect(13, sn.b);
    expect(14, sn.c);
}

static struct abi_check return_struct_func(int x, int y, int a, int b, int c) {
    struct abi_check s;
    s.x = x;
    s.y = y;
    s.z.a = a;
    s.z.b = b;
    s.z.c = c;
    return s;
}

static int sum_struct(int base, struct abi_check s) {
    return base + s.x + s.y + s.z.a + s.z.b + s.z.c;
}

static void struct_return(void) {
    struct abi_check s = return_struct_func(42, 43, 44, 45, 46);
    expect(42, s.x);
    expect(43, s.y);
    expect(44, s.z.a);
    expect(45, s.z.b);
    expect(46, s.z.c);
    expect(21, sum_struct(6, return_struct_func(1, 2, 3, 4, 5)));
    expect(55, sum_struct(sum_struct(0, return_struct_func(1, 2, 3, 4, 5)),
                          return_struct_func(6, 7, 8, 9, 10)));
    expect(99, return_struct_func(1, 2, 3, 99, 4).z.b);
}

static int struct_arg_func_small(int v, struct abi_check_small s) {
    return v + s.x;
}

static void struct_call_small(void) {
    expect(43, struct_arg_func_small(1, (struct abi_check_small){ 42 }));
}

static struct abi_check return_struct_func_decl(struct abi_check s, int x);

static void struct_return_with_decl(void) {
    expect(42, return_struct_func_decl((struct abi_check){}, 42).x);
}

static struct abi_check return_struct_func_decl(struct abi_check s, int x) {
    return (struct abi_check){ x };
}

void testmain() {
    print("struct");
    t1();
    t2();
    t3();
    t4();
    t5();
    t6();
    t7();
    t8();
    t9();
    t10();
    t11();
    t12();
    t13();
    t14();
    unnamed();
    assign();
    arrow();
    incomplete();
    bitfield_basic();
    bitfield_mix();
    bitfield_union();
    bitfield_unnamed();
    bitfield_initializer();
    test_offsetof();
    flexible_member();
    empty_struct();
    struct_call();
    struct_local();
    struct_global();
    struct_return();
    struct_call_small();
    struct_return_with_decl();
}
