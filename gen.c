// Copyright 2012 Rui Ueyama <rui314@gmail.com>
// This program is free software licensed under the MIT license.

#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include "8cc.h"
#include "list.h"

static int TAB = 8;
static List *functions = &EMPTY_LIST;
static char *lbreak;
static char *lcontinue;
static char *lswitch;
static int stackpos;
static FILE *outputfp;
static int is_main;

static void emit_expr(Node *node);
static void emit_decl_init(List *inits, int off);
static void emit_data_int(List *inits, int size, int off, int depth);
static void emit_data(Node *v, int off, int depth);

#define REGAREA_SIZE 304

#define emit(...)        emitf(__LINE__, "\t" __VA_ARGS__)
#define emit_noindent(...)  emitf(__LINE__, __VA_ARGS__)

#ifdef __GNUC__
#define SAVE                                                            \
    int save_hook __attribute__((unused, cleanup(pop_function)));       \
    list_push(functions, (void *)__func__)

static void pop_function(void *ignore) {
    list_pop(functions);
}
#else
#define SAVE
#endif

static char *get_caller_list(void) {
    String *s = make_string();
    for (Iter *i = list_iter(functions); !iter_end(i);) {
        string_appendf(s, "%s", iter_next(i));
        if (!iter_end(i))
            string_appendf(s, " -> ");
    }
    return get_cstring(s);
}

void set_output_file(FILE *fp) {
    outputfp = fp;
}

void close_output_file(void) {
    fclose(outputfp);
}

static void emitf(int line, char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    int col = vfprintf(outputfp, fmt, args);
    va_end(args);

    for (char *p = fmt; *p; p++)
        if (*p == '\t')
            col += TAB - 1;
#ifdef __bfs__
    int space = (28 - col) > 0 ? (30 - col) : 2;
    fprintf(outputfp, "%*c %s:%d\n", space, '#', get_caller_list(), line);
#else
    fprintf(outputfp, " # %s:%d\n", get_caller_list(), line);
#endif
}

static void push(char *reg) {
    SAVE;
    assert(strcmp(reg, "D"));
    emit("mov D, SP");
    emit("add D, -1");
    emit("store %s, D", reg);
    emit("mov SP, D");
    stackpos += 1;
}

static void pop(char *reg) {
    SAVE;
    emit("load %s, SP", reg);
    emit("add SP, 1", reg);
    stackpos -= 1;
    assert(stackpos >= 0);
}

static void emit_gload(Ctype *ctype, char *label, int off) {
    SAVE;
    if (ctype->type == CTYPE_ARRAY) {
        emit("mov A, %s", label);
        if (off)
            emit("add A, %d", off);
        return;
    }
    emit("mov B, %s", label);
    if (off)
        emit("add B, %d", off);
    emit("load A, B");
}

static void emit_toint(Ctype *ctype) {
    SAVE;
    if (ctype->type == CTYPE_FLOAT)
        emit("cvttss2si %%xmm0, %%eax");
    else if (ctype->type == CTYPE_FLOAT)
        emit("cvttsd2si %%xmm0, %%eax");
}

static void emit_lload(Ctype *ctype, char *base, int off) {
    SAVE;
    if (ctype->type == CTYPE_ARRAY) {
        emit("mov A, %s", base);
        if (off)
            emit("add A, %d", off);
    } else if (ctype->type == CTYPE_FLOAT) {
        assert(0);
    } else if (ctype->type == CTYPE_DOUBLE || ctype->type == CTYPE_LDOUBLE) {
        assert(0);
    } else {
        emit("mov B, %s", base);
        if (off)
            emit("add B, %d", off);
        emit("load A, B");
    }
}

static void maybe_convert_bool(Ctype *ctype) {
    if (ctype->type == CTYPE_BOOL) {
        emit("test %%rax, %%rax");
        emit("setne %%al");
    }
}

static void emit_gsave(char *varname, Ctype *ctype, int off) {
    SAVE;
    assert(ctype->type != CTYPE_ARRAY);
    maybe_convert_bool(ctype);
    emit("mov B, %s", varname);
    if (off)
        emit("add B, %d", off);
    emit("store A, B");
}

static void emit_lsave(Ctype *ctype, int off) {
    SAVE;
    if (ctype->type == CTYPE_FLOAT) {
        assert(0);
    } else if (ctype->type == CTYPE_DOUBLE) {
        assert(0);
    } else {
        emit("mov B, BP");
        if (off)
            emit("add B, %d", off);
        emit("store A, B");
    }
}

static void emit_assign_deref_int(Ctype *ctype, int off) {
    SAVE;
    emit("mov C, A");
    emit("load A, SP");
    emit("mov B, A");
    emit("mov A, C");
    if (off)
        emit("add A, %d", off);
    emit("store B, A");
    pop("A");
}

static void emit_assign_deref(Node *var) {
    SAVE;
    push("A");
    emit_expr(var->operand);
    emit_assign_deref_int(var->operand->ctype->ptr, 0);
}

static void emit_pointer_arith(char type, Node *left, Node *right) {
    SAVE;
    emit_expr(left);
    push("B");
    push("A");
    emit_expr(right);
    assert(left->ctype->ptr->size <= 2);
    if (left->ctype->ptr->size == 2)
        emit("add A, A");
    emit("mov B, A");
    pop("A");
    switch (type) {
    case '+': emit("add A, B"); break;
    case '-': emit("sub A, B"); break;
    default: error("invalid operator '%d'", type);
    }
    emit("mov C, A");
    pop("A");
    emit("mov B, A");
    emit("mov A, C");
}

static void emit_zero_filler(int start, int end) {
    emit("mov A, 0");
    emit("mov B, SP");
    for (; start < end; start++) {
        emit("store A, B");
        emit("add B, 1");
    }
}

static void ensure_lvar_init(Node *node) {
    assert(node->type == AST_LVAR);
    if (node->lvarinit) {
        emit_zero_filler(node->loff, node->loff + node->ctype->size);
        emit_decl_init(node->lvarinit, node->loff);
    }
    node->lvarinit = NULL;
}

static void emit_assign_struct_ref(Node *struc, Ctype *field, int off) {
    SAVE;
    switch (struc->type) {
    case AST_LVAR:
        ensure_lvar_init(struc);
        emit_lsave(field, struc->loff + field->offset + off);
        break;
    case AST_GVAR:
        emit_gsave(struc->varname, field, field->offset + off);
        break;
    case AST_STRUCT_REF:
        emit_assign_struct_ref(struc->struc, field, off + struc->ctype->offset);
        break;
    case AST_DEREF:
        push("A");
        emit_expr(struc->operand);
        emit_assign_deref_int(field, field->offset + off);
        break;
    default:
        error("internal error: %s", a2s(struc));
    }
}

static void emit_load_struct_ref(Node *struc, Ctype *field, int off) {
    SAVE;
    switch (struc->type) {
    case AST_LVAR:
        ensure_lvar_init(struc);
        emit_lload(field, "BP", struc->loff + field->offset + off);
        break;
    case AST_GVAR:
        emit_gload(field, struc->varname, field->offset + off);
        break;
    case AST_STRUCT_REF:
        emit_load_struct_ref(struc->struc, field, struc->ctype->offset + off);
        break;
    case AST_DEREF:
        emit_expr(struc->operand);
        emit_lload(field, "A", field->offset + off);
        break;
    default:
        error("internal error: %s", a2s(struc));
    }
}

static void emit_store(Node *var) {
    SAVE;
    switch (var->type) {
    case AST_DEREF: emit_assign_deref(var); break;
    case AST_STRUCT_REF: emit_assign_struct_ref(var->struc, var->ctype, 0); break;
    case AST_LVAR:
        ensure_lvar_init(var);
        emit_lsave(var->ctype, var->loff);
        break;
    case AST_GVAR: emit_gsave(var->varname, var->ctype, 0); break;
    default: error("internal error");
    }
}

static void emit_to_bool(Ctype *ctype) {
    SAVE;
    if (is_flotype(ctype)) {
        assert(0);
    } else {
        emit("cmp $0, %%rax");
        emit("setne %%al");
    }
    emit("movzb %%al, %%eax");
}

static void emit_comp(char *inst, Node *node) {
    SAVE;
    if (is_flotype(node->left->ctype)) {
        assert(0);
    } else {
        emit_expr(node->left);
        push("A");
        emit_expr(node->right);
        emit("mov B, A");
        pop("A");
    }
    emit("%s A, B", inst);
}

static void emit_label(char *label) {
    emit("%s:", label);
}

static void emit_call_builtin(char *fname) {
    char *end = make_label();
    emit("mov A, %s", end);
    push("A");
    emit("jmp %s", fname);
    emit_label(end);
    emit("mov A, B");
}

static void emit_binop_int_arith(Node *node) {
    SAVE;
    emit_expr(node->left);
    push("A");
    emit_expr(node->right);
    emit("mov B, A");
    pop("A");
    switch (node->type) {
        case '+':
            emit("add A, B");
            break;
        case '-':
            emit("sub A, B");
            break;
        case '*':
        case '/':
        case '%':
            push("B");
            push("A");
            if (node->type == '*')
                emit_call_builtin("__builtin_mul");
            else if (node->type == '/')
                emit_call_builtin("__builtin_div");
            else if (node->type == '%')
                emit_call_builtin("__builtin_mod");
            emit("add SP, 2");
            stackpos -= 3;
            break;
        case '^':
        case OP_SAL:
        case OP_SAR:
        case OP_SHR:
            assert(0);
            break;
        default: error("invalid operator '%d'", node->type);
    }
}

static void emit_binop_float_arith(Node *node) {
    assert(0);
}

static void emit_load_convert(Ctype *to, Ctype *from) {
    SAVE;
    if (is_inttype(from) && to->type == CTYPE_FLOAT)
        emit("cvtsi2ss %%eax, %%xmm0");
    else if (is_inttype(from) && to->type == CTYPE_DOUBLE)
        emit("cvtsi2sd %%eax, %%xmm0");
    else if (from->type == CTYPE_FLOAT && to->type == CTYPE_DOUBLE)
        emit("cvtps2pd %%xmm0, %%xmm0");
    else if (from->type == CTYPE_DOUBLE && to->type == CTYPE_FLOAT)
        emit("cvtpd2ps %%xmm0, %%xmm0");
    else if (to->type == CTYPE_BOOL)
        emit_to_bool(from);
    else if (is_inttype(to))
        emit_toint(from);
}

static void emit_ret(void) {
    SAVE;
    if (is_main) {
        emit("exit");
    } else {
        emit("mov SP, BP");
        pop("A");
        emit("mov BP, A");
        pop("A");
        emit("jmp A");
        stackpos += 2;
    }
}

static void emit_binop(Node *node) {
    SAVE;
    if (node->ctype->type == CTYPE_PTR) {
        emit_pointer_arith(node->type, node->left, node->right);
        return;
    }
    switch (node->type) {
    case '<': emit_comp("lt", node); return;
    case '>': emit_comp("gt", node); return;
    case OP_EQ: emit_comp("eq", node); return;
    case OP_GE: emit_comp("ge", node); return;
    case OP_LE: emit_comp("le", node); return;
    case OP_NE: emit_comp("ne", node); return;
    }
    if (is_inttype(node->ctype))
        emit_binop_int_arith(node);
    else if (is_flotype(node->ctype))
        emit_binop_float_arith(node);
    else
        error("internal error");
}

static void emit_save_literal(Node *node, Ctype *totype, int off) {
    int v = node->ival;
    switch (totype->type) {
    case CTYPE_BOOL:
        v = !!v;
    case CTYPE_CHAR:
    case CTYPE_SHORT:
    case CTYPE_INT:
    case CTYPE_LONG:
    case CTYPE_LLONG:
    case CTYPE_PTR: {
        emit("mov B, BP");
        if (off)
            emit("add B, %d", off);
        emit("mov A, %d", v);
        emit("store A, B");
        break;
    }
    case CTYPE_FLOAT:
    case CTYPE_DOUBLE:
        assert(0);
    default:
        error("internal error: <%s> <%s> <%d>", a2s(node), c2s(totype), off);
    }
}

static void emit_addr(Node *node) {
    switch (node->type) {
    case AST_LVAR:
        ensure_lvar_init(node);
        emit("mov A, BP");
        if (node->loff)
            emit("add A, %d", node->loff);
        break;
    case AST_GVAR:
        emit("mov A, %s", node->glabel);
        break;
    case AST_DEREF:
        emit_expr(node->operand);
        break;
    case AST_STRUCT_REF:
        emit_addr(node->struc);
        emit("add A, %d", node->ctype->offset);
        break;
    default:
        error("internal error: %s", a2s(node));
    }
}

static void emit_copy_struct(Node *left, Node *right) {
    push("B");
    push("C");
    emit_addr(right);
    push("A");
    emit_addr(left);
    emit("mov C, A");
    pop("A");
    emit("mov B, A");
    int i = 0;
    for (; i < left->ctype->size; i++) {
        emit("load A, B");
        emit("store A, C");
        emit("add B, 1");
        emit("add C, 1");
    }
    pop("A");
    emit("mov C, A");
    pop("A");
    emit("mov B, A");
}

static void emit_decl_init(List *inits, int off) {
    Iter *iter = list_iter(inits);
    while (!iter_end(iter)) {
        Node *node = iter_next(iter);
        assert(node->type == AST_INIT);
        if (node->initval->type == AST_LITERAL &&
            node->totype->bitsize <= 0) {
            emit_save_literal(node->initval, node->totype, node->initoff + off);
        } else {
            emit_expr(node->initval);
            emit_lsave(node->totype, node->initoff + off);
        }
    }
}

static void emit_uminus(Node *node) {
    emit_expr(node->operand);
    if (is_flotype(node->ctype)) {
        assert(0);
    } else {
        emit("mov B, 0");
        emit("sub B, A");
        emit("mov A, B");
    }
}

static void emit_pre_inc_dec(Node *node, char *op) {
    emit_expr(node->operand);
    emit("%s A, 1", op);
    emit_store(node->operand);
}

static void emit_post_inc_dec(Node *node, char *op) {
    SAVE;
    emit_expr(node->operand);
    push("A");
    emit("%s A, 1", op);
    emit_store(node->operand);
    pop("A");
}

static void emit_je(char *label) {
    emit("jeq %s, A, 0", label);
}

static void emit_jmp(char *label) {
    emit("jmp %s", label);
}

static void emit_literal(Node *node) {
    SAVE;
    switch (node->ctype->type) {
    case CTYPE_BOOL:
    case CTYPE_CHAR:
        emit("mov A, %d", node->ival);
        break;
    case CTYPE_INT:
        emit("mov A, %d", node->ival);
        break;
    case CTYPE_LONG:
    case CTYPE_LLONG: {
        emit("mov A, %lu", node->ival);
        break;
    }
    case CTYPE_FLOAT: {
        assert(0);
        break;
    }
    case CTYPE_DOUBLE:
    case CTYPE_LDOUBLE: {
        assert(0);
        break;
    }
    default:
        error("internal error");
    }
}

static void emit_literal_string(Node *node) {
    SAVE;
    if (!node->slabel) {
        node->slabel = make_label();
        emit_noindent(".data");
        emit_label(node->slabel);
        emit(".string \"%s\"", quote_cstring(node->sval));
        emit_noindent(".text");
    }
    emit("mov A, %s", node->slabel);
}

static void emit_lvar(Node *node) {
    SAVE;
    ensure_lvar_init(node);
    emit_lload(node->ctype, "BP", node->loff);
}

static void emit_gvar(Node *node) {
    SAVE;
    emit_gload(node->ctype, node->glabel, 0);
}

static void classify_args(List *ints, List *args) {
    SAVE;
    Iter *iter = list_iter(args);
    while (!iter_end(iter)) {
        Node *v = iter_next(iter);
        assert(!is_flotype(v->ctype));
        list_push(ints, v);
    }
}

static void emit_args(List *vals) {
    SAVE;
    Iter *iter = list_iter(vals);
    while (!iter_end(iter)) {
        Node *v = iter_next(iter);
        emit_expr(v);
        assert(!is_flotype(v->ctype));
        push("A");
    }
}

static void maybe_booleanize_retval(Ctype *ctype) {
    if (ctype->type == CTYPE_BOOL) {
        emit("movzx %%al, %%rax");
    }
}

static void emit_call(Node *node) {
    bool isptr = (node->type == AST_FUNCPTR_CALL);
    char *end = make_label();
    if (isptr) {
        emit_expr(node->fptr);
        emit("mov C, A");
    }
    emit("mov A, %s", end);
    push("A");
    if (isptr)
        emit("jmp C");
    else
        emit("jmp %s", node->fname);
    emit_label(end);
    emit("mov A, B");
    stackpos -= 1;
}

static void emit_func_call(Node *node) {
    SAVE;
    int opos = stackpos;

    List *ints = make_list();

    classify_args(ints, node->args);

    emit_args(list_reverse(ints));

    if (!node->fname) {
        emit_call(node);
    } else if (!strcmp(node->fname, "exit")) {
        emit("exit");
    } else if (!strcmp(node->fname, "putchar")) {
        emit("putc A");
    } else if (!strcmp(node->fname, "getchar")) {
        char *end = make_label();
        emit("getc A");
        emit("jne %s, A, 0", end);
        emit("mov A, -1");
        emit_label(end);
    } else {
        emit_call(node);
    }
    if (list_len(ints))
        emit("add SP, %d", list_len(ints));
    stackpos -= list_len(ints);
    assert(opos == stackpos);
}

static void emit_decl(Node *node) {
    SAVE;
    if (!node->declinit)
        return;
    emit_zero_filler(node->declvar->loff,
                     node->declvar->loff + node->declvar->ctype->size);
    emit_decl_init(node->declinit, node->declvar->loff);
}

static void emit_conv(Node *node) {
    SAVE;
    emit_expr(node->operand);
    emit_load_convert(node->ctype, node->operand->ctype);
}

static void emit_deref(Node *node) {
    SAVE;
    emit_expr(node->operand);
    emit_lload(node->operand->ctype->ptr, "A", 0);
    emit_load_convert(node->ctype, node->operand->ctype->ptr);
}

static void emit_ternary(Node *node) {
    SAVE;
    emit_expr(node->cond);
    char *ne = make_label();
    emit_je(ne);
    if (node->then)
        emit_expr(node->then);
    if (node->els) {
        char *end = make_label();
        emit_jmp(end);
        emit_label(ne);
        emit_expr(node->els);
        emit_label(end);
    } else {
        emit_label(ne);
    }
}

#define SET_JUMP_LABELS(brk, cont)              \
    char *obreak = lbreak;                      \
    char *ocontinue = lcontinue;                \
    lbreak = brk;                               \
    lcontinue = cont
#define RESTORE_JUMP_LABELS()                   \
    lbreak = obreak;                            \
    lcontinue = ocontinue

static void emit_for(Node *node) {
    SAVE;
    if (node->forinit)
        emit_expr(node->forinit);
    char *begin = make_label();
    char *step = make_label();
    char *end = make_label();
    SET_JUMP_LABELS(end, step);
    emit_label(begin);
    if (node->forcond) {
        emit_expr(node->forcond);
        emit_je(end);
    }
    if (node->forbody)
        emit_expr(node->forbody);
    emit_label(step);
    if (node->forstep)
        emit_expr(node->forstep);
    emit_jmp(begin);
    emit_label(end);
    RESTORE_JUMP_LABELS();
}

static void emit_while(Node *node) {
    SAVE;
    char *begin = make_label();
    char *end = make_label();
    SET_JUMP_LABELS(end, begin);
    emit_label(begin);
    emit_expr(node->forcond);
    emit_je(end);
    if (node->forbody)
        emit_expr(node->forbody);
    emit_jmp(begin);
    emit_label(end);
    RESTORE_JUMP_LABELS();
}

static void emit_do(Node *node) {
    SAVE;
    char *begin = make_label();
    char *end = make_label();
    SET_JUMP_LABELS(end, begin);
    emit_label(begin);
    if (node->forbody)
        emit_expr(node->forbody);
    emit_expr(node->forcond);
    emit_je(end);
    emit_jmp(begin);
    emit_label(end);
    RESTORE_JUMP_LABELS();
}

#undef SET_JUMP_LABELS
#undef RESTORE_JUMP_LABELS

static void emit_switch(Node *node) {
    SAVE;
    char *oswitch = lswitch, *obreak = lbreak;
    emit_expr(node->switchexpr);
    lswitch = make_label();
    lbreak = make_label();
    emit_jmp(lswitch);
    if (node->switchbody)
        emit_expr(node->switchbody);
    emit_label(lswitch);
    emit_label(lbreak);
    lswitch = oswitch;
    lbreak = obreak;
}

static void emit_case(Node *node) {
    SAVE;
    if (!lswitch)
        error("stray case label");
    char *skip = make_label();
    emit_jmp(skip);
    emit_label(lswitch);
    lswitch = make_label();
    if (node->casebeg == node->caseend) {
        emit("jne %s, A, %d", lswitch, node->casebeg);
    } else {
        emit("jlt %s, A, %d", lswitch, node->casebeg);
        emit("jgt %s, A, %d", lswitch, node->caseend);
    }
    emit_label(skip);
}

static void emit_default(Node *node) {
    SAVE;
    if (!lswitch)
        error("stray case label");
    emit_label(lswitch);
    lswitch = make_label();
}

static void emit_goto(Node *node) {
    SAVE;
    assert(node->newlabel);
    emit_jmp(node->newlabel);
}

static void emit_return(Node *node) {
    SAVE;
    if (node->retval) {
        emit_expr(node->retval);
        maybe_booleanize_retval(node->retval->ctype);
        emit("mov B, A");
    }
    emit_ret();
}

static void emit_break(Node *node) {
    SAVE;
    if (!lbreak)
        error("stray break statement");
    emit_jmp(lbreak);
}

static void emit_continue(Node *node) {
    SAVE;
    if (!lcontinue)
        error("stray continue statement");
    emit_jmp(lcontinue);
}

static void emit_compound_stmt(Node *node) {
    SAVE;
    for (Iter *i = list_iter(node->stmts); !iter_end(i);)
        emit_expr(iter_next(i));
}

static void emit_logand(Node *node) {
    SAVE;
    char *end = make_label();
    emit_expr(node->left);
    emit("mov B, 0");
    emit("jeq %s, A, 0", end);
    emit_expr(node->right);
    emit("mov B, A");
    emit("ne B, 0");
    emit_label(end);
    emit("mov A, B");
}

static void emit_logor(Node *node) {
    SAVE;
    char *end = make_label();
    emit_expr(node->left);
    emit("mov B, 1");
    emit("jne %s, A, 0", end);
    emit_expr(node->right);
    emit("mov B, A");
    emit("ne B, 0");
    emit_label(end);
    emit("mov A, B");
}

static void emit_lognot(Node *node) {
    SAVE;
    emit_expr(node->operand);
    emit("eq A, 0");
}

static void emit_bitand(Node *node) {
    SAVE;
    emit_expr(node->left);
    push("rax");
    emit_expr(node->right);
    pop("rcx");
    emit("and %%rcx, %%rax");
}

static void emit_bitor(Node *node) {
    SAVE;
    emit_expr(node->left);
    push("rax");
    emit_expr(node->right);
    pop("rcx");
    emit("or %%rcx, %%rax");
}

static void emit_bitnot(Node *node) {
    SAVE;
    emit_expr(node->left);
    emit("not %%rax");
}

static void emit_cast(Node *node) {
    SAVE;
    emit_expr(node->operand);
    emit_load_convert(node->ctype, node->operand->ctype);
    return;
}

static void emit_comma(Node *node) {
    SAVE;
    emit_expr(node->left);
    emit_expr(node->right);
}

static void emit_assign(Node *node) {
    SAVE;
    if (node->left->ctype->type == CTYPE_STRUCT) {
        emit_copy_struct(node->left, node->right);
    } else {
        emit_expr(node->right);
        emit_load_convert(node->ctype, node->right->ctype);
        emit_store(node->left);
    }
}

static void emit_label_addr(Node *node) {
    SAVE;
    emit("mov $%s, %%rax", node->newlabel);
}

static void emit_computed_goto(Node *node) {
    SAVE;
    emit_expr(node->operand);
    emit("jmp *%%rax");
}

static void emit_expr(Node *node) {
    SAVE;
    switch (node->type) {
    case AST_LITERAL: emit_literal(node); return;
    case AST_STRING:  emit_literal_string(node); return;
    case AST_LVAR:    emit_lvar(node); return;
    case AST_GVAR:    emit_gvar(node); return;
    case AST_FUNCALL:
    case AST_FUNCPTR_CALL:
        emit_func_call(node);
        return;
    case AST_DECL:    emit_decl(node); return;
    case AST_CONV:    emit_conv(node); return;
    case AST_ADDR:    emit_addr(node->operand); return;
    case AST_DEREF:   emit_deref(node); return;
    case AST_IF:
    case AST_TERNARY:
        emit_ternary(node);
        return;
    case AST_FOR:     emit_for(node); return;
    case AST_WHILE:   emit_while(node); return;
    case AST_DO:      emit_do(node); return;
    case AST_SWITCH:  emit_switch(node); return;
    case AST_CASE:    emit_case(node); return;
    case AST_DEFAULT: emit_default(node); return;
    case AST_GOTO:    emit_goto(node); return;
    case AST_LABEL:
        if (node->newlabel)
            emit_label(node->newlabel);
        return;
    case AST_RETURN:  emit_return(node); return;
    case AST_BREAK:   emit_break(node); return;
    case AST_CONTINUE: emit_continue(node); return;
    case AST_COMPOUND_STMT: emit_compound_stmt(node); return;
    case AST_STRUCT_REF:
        emit_load_struct_ref(node->struc, node->ctype, 0);
        return;
    case AST_VA_START: assert(0); return;
    case AST_VA_ARG:   assert(0); return;
    case OP_UMINUS:    emit_uminus(node); return;
    case OP_PRE_INC:   emit_pre_inc_dec(node, "add"); return;
    case OP_PRE_DEC:   emit_pre_inc_dec(node, "sub"); return;
    case OP_POST_INC:  emit_post_inc_dec(node, "add"); return;
    case OP_POST_DEC:  emit_post_inc_dec(node, "sub"); return;
    case '!': emit_lognot(node); return;
    case '&': emit_bitand(node); return;
    case '|': emit_bitor(node); return;
    case '~': emit_bitnot(node); return;
    case OP_LOGAND: emit_logand(node); return;
    case OP_LOGOR:  emit_logor(node); return;
    case OP_CAST:   emit_cast(node); return;
    case ',': emit_comma(node); return;
    case '=': emit_assign(node); return;
    case OP_LABEL_ADDR: emit_label_addr(node); return;
    case AST_COMPUTED_GOTO: emit_computed_goto(node); return;
    default:
        emit_binop(node);
    }
}

static void emit_zero(int size) {
    SAVE;
    for (; size > 0; size--)     emit(".long 0");
}

static void emit_padding(Node *node, int off) {
    SAVE;
    int diff = node->initoff - off;
    assert(diff >= 0);
    emit_zero(diff);
}

static void emit_data_addr(Node *operand, int depth) {
    switch (operand->type) {
    case AST_LVAR: {
        char *label = make_label();
        emit(".data %d", depth + 1);
        emit_label(label);
        emit_data_int(operand->lvarinit, operand->ctype->size, 0, depth + 1);
        emit(".data %d", depth);
        emit(".long %s", label);
        return;
    }
    case AST_GVAR:
        emit(".long %s", operand->varname);
        return;
    default:
        error("internal error");
    }
}

static void emit_data_charptr(char *s, int depth) {
    char *label = make_label();
    emit(".data %d", depth + 1);
    emit_label(label);
    emit(".string \"%s\"", quote_cstring(s));
    emit(".data %d", depth);
    emit(".long %s", label);
}

static void emit_data_primtype(Ctype *ctype, Node *val) {
    switch (ctype->type) {
    case CTYPE_FLOAT: {
        assert(0);
        break;
    }
    case CTYPE_DOUBLE:
        assert(0);
        break;
    case CTYPE_BOOL:
        emit(".long %d", !!eval_intexpr(val));
        break;
    case CTYPE_CHAR:
    case CTYPE_INT:
    case CTYPE_SHORT:
    case CTYPE_LONG:
    case CTYPE_LLONG:
    case CTYPE_PTR:
        emit(".long %d", eval_intexpr(val));
        break;
    default:
        error("don't know how to handle\n  <%s>\n  <%s>", c2s(ctype), a2s(val));
    }
}

static void emit_data_int(List *inits, int size, int off, int depth) {
    SAVE;
    Iter *iter = list_iter(inits);
    while (!iter_end(iter) && 0 < size) {
        Node *node = iter_next(iter);
        Node *v = node->initval;
        emit_padding(node, off);
        if (node->totype->bitsize > 0) {
            assert(node->totype->bitoff == 0);
            long data = eval_intexpr(v);
            Ctype *totype = node->totype;
            while (!iter_end(iter)) {
                node = iter_next(iter);
                if (node->totype->bitsize <= 0) {
                    break;
                }
                v = node->initval;
                totype = node->totype;
                //data |= ((((long)1 << totype->bitsize) - 1) & eval_intexpr(v)) << totype->bitoff;
                assert(0);
            }
            emit_data_primtype(totype, &(Node){ AST_LITERAL, totype, .ival = data });
            off += totype->size;
            size -= totype->size;
            if (iter_end(iter))
                break;
        } else {
            off += node->totype->size;
            size -= node->totype->size;
        }
        if (v->type == AST_ADDR) {
            emit_data_addr(v->operand, depth);
            continue;
        }
        if (v->type == AST_LVAR && v->lvarinit) {
            emit_data_int(v->lvarinit, v->ctype->size, 0, depth);
            continue;
        }
        bool is_char_ptr = (v->ctype->type == CTYPE_ARRAY && v->ctype->ptr->type == CTYPE_CHAR);
        if (is_char_ptr) {
            emit_data_charptr(v->sval, depth);
            continue;
        }
        emit_data_primtype(node->totype, node->initval);
    }
    emit_zero(size);
}

static void emit_data(Node *v, int off, int depth) {
    SAVE;
    emit(".data %d", depth);
    emit_noindent("%s:", v->declvar->varname);
    emit_data_int(v->declinit, v->declvar->ctype->size, off, depth);
}

static void emit_bss(Node *v) {
    SAVE;
    emit(".data");
    emit(".lcomm %s, %d", v->declvar->varname, v->declvar->ctype->size);
}

static void emit_global_var(Node *v) {
    SAVE;
    if (v->declinit)
        emit_data(v, 0, 0);
    else
        emit_bss(v);
}

static void assign_func_param_offsets(List *params, int off) {
    int arg = 2;
    for (Iter *i = list_iter(params); !iter_end(i);) {
        Node *v = iter_next(i);
        if (is_flotype(v->ctype))
            assert(0);
        v->loff = arg++;
    }
}

static void emit_func_prologue(Node *func) {
    SAVE;
    emit(".text");
    emit_noindent("%s:", func->fname);

    push("BP");
    emit("mov BP, SP");
    int off = 0;
    assign_func_param_offsets(func->params, off);

    int localarea = 0;
    for (Iter *i = list_iter(func->localvars); !iter_end(i);) {
        Node *v = iter_next(i);
        int size = v->ctype->size;
        off -= size;
        v->loff = off;
        localarea += size;
    }
    if (localarea) {
        emit("sub SP, %d", localarea);
        stackpos += localarea;
    }
}

void emit_toplevel(Node *v) {
    stackpos = 1;
    if (v->type == AST_FUNC) {
        is_main = !strcmp(v->fname, "main");
        emit_func_prologue(v);
        emit_expr(v->body);
        emit_ret();
        is_main = 0;
    } else if (v->type == AST_DECL) {
        emit_global_var(v);
    } else {
        error("internal error");
    }
}
