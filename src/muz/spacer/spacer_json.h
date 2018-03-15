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
#include "ref.h"
#include "ref_vector.h"

class ast;

class ast_manager;

namespace spacer {

    class lemma;

    typedef sref_vector<lemma> lemma_ref_vector;

    class context;

    class pob;

    std::ostream &json_marshal(std::ostream &out, ast *t, ast_manager &m);

    std::ostream &json_marshal(std::ostream &out, lemma *l);

    std::ostream &json_marshal(std::ostream &out, lemma_ref_vector &lemmas);


    class json_marshaller {
        context *m_ctx;
        std::map<pob*, std::map<unsigned, lemma_ref_vector>> m_relations;

    public:
        json_marshaller(context *ctx) : m_ctx(ctx) {}

        void register_lemma(lemma *l);

        void register_pob(pob *p);

        std::ostream &marshal(std::ostream &out) const;
    };

}


#endif //Z3_SPACER_JSON_H
