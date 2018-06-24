/**++
Copyright (c) 2017 Microsoft Corporation and Matteo Marescotti

Module Name:

    spacer_json.h

Abstract:

    SPACER json marshalling support

Author:

    Matteo Marescotti

Notes:

--*/

#ifndef Z3_SPACER_JSON_H
#define Z3_SPACER_JSON_H

#include<iostream>
#include<map>
#include "util/ref.h"
#include "util/ref_vector.h"

class ast;

class ast_manager;

namespace spacer {

class lemma;
typedef sref_vector<lemma> lemma_ref_vector;
class context;
class pob;


class json_marshaller {
    context *m_ctx;
    bool m_old_style;
    std::map<pob*, std::map<unsigned, lemma_ref_vector>> m_relations;

    void marshal_lemmas_old(std::ostream &out) const;
    void marshal_lemmas_new(std::ostream &out) const;
public:
    json_marshaller(context *ctx, bool old_style = false) :
        m_ctx(ctx), m_old_style(old_style)  {}

    void register_lemma(lemma *l);

    void register_pob(pob *p);

    std::ostream &marshal(std::ostream &out) const;
};

}


#endif //Z3_SPACER_JSON_H
