/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_matrix.cpp

Abstract:
    a matrix

Author:
    Bernhard Gleiss

Revision History:


--*/
#include "muz/spacer/spacer_matrix.h"

namespace spacer
{
    spacer_matrix::spacer_matrix(unsigned m, unsigned n) : m_num_rows(m), m_num_cols(n)
    {
        for (unsigned i=0; i < m; ++i)
        {
            vector<rational> v;
            for (unsigned j=0; j < n; ++j)
            {
                v.push_back(rational(0));
            }
            m_matrix.push_back(v);
        }
    }

    unsigned spacer_matrix::num_rows()
    {
        return m_num_rows;
    }

    unsigned spacer_matrix::num_cols()
    {
        return m_num_cols;
    }

    const rational& spacer_matrix::get(unsigned int i, unsigned int j)
    {
        SASSERT(i < m_num_rows);
        SASSERT(j < m_num_cols);

        return m_matrix[i][j];
    }

    void spacer_matrix::set(unsigned int i, unsigned int j, const rational& v)
    {
        SASSERT(i < m_num_rows);
        SASSERT(j < m_num_cols);

        m_matrix[i][j] = v;
    }

    unsigned spacer_matrix::perform_gaussian_elimination()
    {
        unsigned i=0;
        unsigned j=0;
        while(i < m_matrix.size() && j < m_matrix[0].size())
        {
            // find maximal element in column with row index bigger or equal i
            rational max = m_matrix[i][j];
            unsigned max_index = i;

            for (unsigned k=i+1; k < m_matrix.size(); ++k)
            {
                if (max < m_matrix[k][j])
                {
                    max = m_matrix[k][j];
                    max_index = k;
                }
            }

            if (max.is_zero()) // skip this column
            {
                ++j;
            }
            else
            {
                // reorder rows if necessary
                vector<rational> tmp = m_matrix[i];
                m_matrix[i] = m_matrix[max_index];
                m_matrix[max_index] = m_matrix[i];

                // normalize row
                rational pivot = m_matrix[i][j];
                if (!pivot.is_one())
                {
                    for (unsigned k=0; k < m_matrix[i].size(); ++k)
                    {
                        m_matrix[i][k] = m_matrix[i][k] / pivot;
                    }
                }

                // subtract row from all other rows
                for (unsigned k=1; k < m_matrix.size(); ++k)
                {
                    if (k != i)
                    {
                        rational factor = m_matrix[k][j];
                        for (unsigned l=0; l < m_matrix[k].size(); ++l)
                        {
                            m_matrix[k][l] = m_matrix[k][l] - (factor * m_matrix[i][l]);
                        }
                    }
                }

                ++i;
                ++j;
            }
        }

        if (get_verbosity_level() >= 1)
        {
            SASSERT(m_matrix.size() > 0);
        }

        return i; //i points to the row after the last row which is non-zero
    }

    void spacer_matrix::print_matrix()
    {
        verbose_stream() << "\nMatrix\n";
        for (const auto& row : m_matrix)
        {
            for (const auto& element : row)
            {
                verbose_stream() << element << ", ";
            }
            verbose_stream() << "\n";
        }
        verbose_stream() << "\n";
    }
    void spacer_matrix::normalize()
    {
        rational den = rational::one();
        for (unsigned i=0; i < m_num_rows; ++i)
        {
            for (unsigned j=0; j < m_num_cols; ++j)
            {
                den = lcm(den, denominator(m_matrix[i][j]));
            }
        }
        for (unsigned i=0; i < m_num_rows; ++i)
        {
            for (unsigned j=0; j < m_num_cols; ++j)
            {
                m_matrix[i][j] = den * m_matrix[i][j];
                SASSERT(m_matrix[i][j].is_int());
            }
        }
    }
}
