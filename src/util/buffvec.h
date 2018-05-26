/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    buffvec.h

Author:

    Daniel Schemmel 2019-2-23

--*/

#pragma once

#include "util/debug.h"
#include "util/memory_manager.h"

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <type_traits>
#include <iterator>
#include <utility>
#include <memory>
#include <algorithm>

namespace buffvec_detail {
    // copy_into, move_into and destroy can reasonably be flattened to memcpy by the optimizer, we are just being paranoid here
#if defined(__GNUC__) && !defined(__clang__) && __GNUC__ >= 8
#pragma GCC diagnostic push
    // in this context it should be legal to use `std::memcpy` if the target type is trivially move constructible and possibly
    // trivially destructible. GCC 8, however, requires the target type to be (fully) trivially copyable, or it will warn.
#pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
    template<typename T>
    inline typename std::enable_if<std::is_trivially_move_constructible<typename std::remove_cv<T>::type>::value>::type
    copy_into(T* destination, T const* source, std::size_t count) {
        if(count) { // destination or source may only be nullptrs if count is 0
            SASSERT(source);
            SASSERT(destination);
            std::memcpy(destination, source, count * sizeof(T));
        }
    }

#if defined(_MSC_VER)
    template<typename T>
    inline typename std::enable_if<!std::is_trivially_move_constructible<typename std::remove_cv<T>::type>::value>::type
    copy_into(T* destination, T const* source, std::size_t count) {
        std::uninitialized_copy(
            stdext::make_unchecked_array_iterator(source),
            stdext::make_unchecked_array_iterator(source + count),
            stdext::make_unchecked_array_iterator(destination)
        );
    }
#else
    template<typename T>
    inline typename std::enable_if<!std::is_trivially_move_constructible<typename std::remove_cv<T>::type>::value>::type
    copy_into(T* destination, T const* source, std::size_t count) {
        std::uninitialized_copy(source, source + count, destination);
    }
#endif

    template<typename T>
    inline typename std::enable_if<std::is_trivially_move_constructible<typename std::remove_cv<T>::type>::value>::type
    move_into(T* destination, T* source, std::size_t count) {
        if(count) { // destination or source may only be nullptrs if count is 0
            SASSERT(source);
            SASSERT(destination);
            std::memcpy(destination, source, count * sizeof(T));
        }
    }

#if defined(_MSC_VER)
    template<typename T>
    inline typename std::enable_if<!std::is_trivially_move_constructible<typename std::remove_cv<T>::type>::value>::type
    move_into(T* destination, T* source, std::size_t count) {
        std::uninitialized_copy(
            std::make_move_iterator(stdext::make_unchecked_array_iterator(source)),
            std::make_move_iterator(stdext::make_unchecked_array_iterator(source + count)),
            stdext::make_unchecked_array_iterator(destination)
        );
    }
#else
    template<typename T>
    inline typename std::enable_if<!std::is_trivially_move_constructible<typename std::remove_cv<T>::type>::value>::type
    move_into(T* destination, T* source, std::size_t count) {
        std::uninitialized_copy(std::make_move_iterator(source), std::make_move_iterator(source + count), destination);
    }
#endif

    template<typename T>
    inline typename std::enable_if<std::is_trivially_move_constructible<typename std::remove_cv<T>::type>::value>::type
    move_around(T* destination, T* source, std::size_t count) {
        if(count) { // destination or source may only be nullptrs if count is 0
            SASSERT(destination);
            SASSERT(source);
            std::memmove(destination, source, count * sizeof(typename std::remove_cv<T>::type));
        }
    }

    template<typename T>
    inline typename std::enable_if<!std::is_trivially_move_constructible<typename std::remove_cv<T>::type>::value>::type
    move_around(T* destination, T* source, std::size_t count) {
        if(destination < source) {
            for(std::size_t i = 0; i < count; ++i) {
                new(destination + i) T(std::move(source[i]));
                source[i].~T();
            }
        } else if(destination > source) {
            for(std::size_t i = count; i > 0; ) {
                --i;
                new(destination + i) T(std::move(source[i]));
                source[i].~T();
            }
        } // else destination == source: NOP
    }

    template<typename T>
    inline typename std::enable_if<!std::is_trivially_destructible<typename std::remove_cv<T>::type>::value>::type
    destroy(T* begin, T* end)
    noexcept(std::is_nothrow_destructible<typename std::remove_cv<T>::type>::value) {
        using actual_t = typename std::remove_cv<T>::type;
        // std::destroy is C++17 only
        for(; begin < end; ++begin) {
            begin->~actual_t();
        }
    }

    template<typename T>
    inline typename std::enable_if<std::is_trivially_destructible<typename std::remove_cv<T>::type>::value>::type
    destroy(T* /*begin*/, T* /*end*/)
    noexcept {
        // nothing to do
    }
#if defined(__GNUC__) && !defined(__clang__) && __GNUC__ >= 8
#pragma GCC diagnostic pop // -Wclass-memaccess
#endif
}

//----------------------------- vector that stores INITIAL_CAPACITY elements locally -----------------------------//

template<typename T, typename SZ, std::size_t INITIAL_CAPACITY>
class buffvec {
    static_assert(std::numeric_limits<SZ>::is_integer, "SZ must be an unsigned integer type of reasonable size");
    static_assert(!std::numeric_limits<SZ>::is_signed, "SZ must be an unsigned integer type of reasonable size");
    static_assert(std::numeric_limits<SZ>::digits >= 8, "SZ must be an unsigned integer type of reasonable size");
    static_assert(std::numeric_limits<SZ>::digits <= std::numeric_limits<std::size_t>::digits, "SZ must be an unsigned integer type of reasonable size");
    static_assert(static_cast<SZ>(INITIAL_CAPACITY) == INITIAL_CAPACITY, "INITIAL_CAPACITY is too large for the chosen size_type SZ");
    static_assert(INITIAL_CAPACITY > 0, "In this specialization, INITIAL_CAPACITY must be non-zero");

public:
    using value_type = T;
    using size_type = SZ;
    using difference_type = std::ptrdiff_t;
    using reference = value_type&;
    using const_reference = value_type const&;
    using pointer = value_type*;
    using const_pointer = value_type const*;
    using iterator = pointer;
    using const_iterator = const_pointer;
    using reverse_iterator = std::reverse_iterator<iterator>;
    using const_reverse_iterator = std::reverse_iterator<const_iterator>;

    static constexpr const size_type initial_capacity = static_cast<size_type>(INITIAL_CAPACITY);

private:
    using initial_buffer_type = typename std::aligned_union<0, value_type[initial_capacity]>::type;

    pointer m_data = reinterpret_cast<pointer>(&m_initial_buffer);
    size_type m_size = 0;
    size_type m_capacity = initial_capacity;
    initial_buffer_type m_initial_buffer;

    inline pointer ptr() noexcept { return m_data; }
    inline const_pointer ptr() const noexcept { return m_data; }

    inline size_type next_capacity() const noexcept {
        auto const cap = capacity();
        return cap == 0 ? 2 : 2 * cap;
    }

    template<typename U = value_type>
    typename std::enable_if<std::is_trivially_move_constructible<typename std::remove_cv<U>::type>::value && std::is_trivially_destructible<typename std::remove_cv<U>::type>::value>::type
    reallocate(size_type const new_capacity) {
        SASSERT(new_capacity >= size());
        std::size_t const new_bytesize = static_cast<std::size_t>(new_capacity) * sizeof(value_type);

        if(m_data != reinterpret_cast<pointer>(&m_initial_buffer)) {
            m_data = reinterpret_cast<pointer>(memory::reallocate(m_data, new_bytesize));
        } else {
            pointer const buffvec = reinterpret_cast<pointer>(memory::allocate(new_bytesize));
            buffvec_detail::move_into(buffvec, m_data, m_size);
            m_data = buffvec;
        }
        m_capacity = new_capacity;
    }

    template<typename U = value_type>
    typename std::enable_if<!std::is_trivially_move_constructible<typename std::remove_cv<U>::type>::value || !std::is_trivially_destructible<typename std::remove_cv<U>::type>::value>::type
    reallocate(size_type const new_capacity) {
        SASSERT(new_capacity >= size());
        std::size_t const new_bytesize = static_cast<std::size_t>(new_capacity) * sizeof(value_type);
        pointer const buffvec = reinterpret_cast<pointer>(memory::allocate(new_bytesize));

        buffvec_detail::move_into(buffvec, m_data, m_size);
        buffvec_detail::destroy(m_data, m_data + m_size);
        if(m_data != reinterpret_cast<pointer>(&m_initial_buffer)) {
            memory::deallocate(m_data);
        }

        m_data = buffvec;
        m_capacity = new_capacity;
    }

public:
    constexpr buffvec() noexcept = default;

    buffvec(buffvec const& other) {
        size_type const pos = other.m_size;
        m_size = pos;
        if(pos <= initial_capacity) {
            m_data = reinterpret_cast<pointer>(&m_initial_buffer);
            m_capacity = initial_capacity;
        } else {
            m_data = reinterpret_cast<pointer>(memory::allocate(static_cast<std::size_t>(pos) * sizeof(value_type)));
            m_capacity = pos;
        }
        buffvec_detail::copy_into(m_data, other.m_data, pos);
    }

    buffvec& operator=(buffvec const& other) {
        if(this != &other) {
            clear();
            _reserve(other.m_size);
            m_size = other.m_size;
            buffvec_detail::copy_into(m_data, other.m_data, m_size);
        }
        return *this;
    }

    // Depending on initial_capacity, move construction may still be very expensive
    buffvec(buffvec&& other) {
        if(other.m_data != reinterpret_cast<pointer>(&other.m_initial_buffer)) {
            m_data = other.m_data;
            m_size = other.m_size;
            m_capacity = other.m_capacity;
            other.m_data = reinterpret_cast<pointer>(&other.m_initial_buffer);
            other.m_size = 0;
            other.m_capacity = initial_capacity;
        } else {
            m_data = reinterpret_cast<pointer>(&m_initial_buffer);
            m_size = other.m_size;
            m_capacity = initial_capacity;
            buffvec_detail::move_into(m_data, other.m_data, m_size);
            buffvec_detail::destroy(other.begin(), other.end()); // would happen during destruction ´other´ anyway
            other.m_size = 0;
        }
    }

    // Depending on initial_capacity, move assignment may still be very expensive
    buffvec& operator=(buffvec&& other) {
        using std::swap;
        if(this != &other) {
            if(other.m_data != reinterpret_cast<pointer>(&other.m_initial_buffer)) {
                if(m_data != reinterpret_cast<pointer>(&m_initial_buffer)) {
                    swap(m_data, other.m_data);
                    swap(m_size, other.m_size);
                    swap(m_capacity, other.m_capacity);
                } else {
                    buffvec_detail::destroy(begin(), end());
                    m_data = other.m_data;
                    m_size = other.m_size;
                    m_capacity = other.m_capacity;
                    other.m_data = reinterpret_cast<pointer>(&other.m_initial_buffer);
                    other.m_size = 0;
                    other.m_capacity = initial_capacity;
                }
            } else {
                buffvec_detail::destroy(begin(), end());
                m_size = other.m_size;
                buffvec_detail::move_into(m_data, other.m_data, m_size);
            }
        }
        return *this;
    }

    ~buffvec() {
        buffvec_detail::destroy(begin(), end());
        if(m_data != reinterpret_cast<pointer>(&m_initial_buffer)) {
            memory::deallocate(m_data);
        }
    }

    buffvec(size_type count, value_type const& elem) {
        m_size = count;
        if(count <= initial_capacity) {
            m_data = reinterpret_cast<pointer>(&m_initial_buffer);
            m_capacity = initial_capacity;
        } else {
            m_data = reinterpret_cast<pointer>(memory::allocate(static_cast<std::size_t>(count) * sizeof(value_type)));
            m_capacity = count;
        }
        for(size_type i = 0; i < count; ++i) {
            ::new(m_data + i) value_type(elem);
        }
    }

    friend void swap(buffvec& lhs, buffvec& rhs) {
        using std::swap;
        if(lhs.m_data != reinterpret_cast<pointer>(&lhs.m_initial_buffer)) {
            if(rhs.m_data != reinterpret_cast<pointer>(&rhs.m_initial_buffer)) {
                swap(lhs.m_data, rhs.m_data);
                swap(lhs.m_size, rhs.m_size);
                swap(lhs.m_capacity, rhs.m_capacity);
            } else {
                buffvec_detail::move_into(reinterpret_cast<pointer>(&lhs.m_initial_buffer), rhs.m_data, rhs.m_size);
                buffvec_detail::destroy(rhs.m_data, rhs.m_data + rhs.m_size);
                rhs.m_data = lhs.m_data;
                rhs.m_capacity = rhs.m_capacity;
                lhs.m_data = reinterpret_cast<pointer>(&lhs.m_initial_buffer);
                lhs.m_capacity = initial_capacity;
            }
        } else {
            if(rhs.m_data != reinterpret_cast<pointer>(&rhs.m_initial_buffer)) {
                buffvec_detail::move_into(reinterpret_cast<pointer>(&rhs.m_initial_buffer), lhs.m_data, lhs.m_size);
                buffvec_detail::destroy(lhs.m_data, lhs.m_data + lhs.m_size);
                lhs.m_data = rhs.m_data;
                lhs.m_capacity = lhs.m_capacity;
                rhs.m_data = reinterpret_cast<pointer>(&rhs.m_initial_buffer);
                rhs.m_capacity = initial_capacity;
            } else {
                // since initial_buffer_type may be large, we don't want to put one on the stack
                // this way we even potentially gain some speed, as we eliminate one O(n) element-wise copy
                SASSERT(lhs.m_capacity == initial_capacity);
                SASSERT(rhs.m_capacity == initial_capacity);
                rhs.m_capacity = rhs.next_capacity();
                pointer buffer = reinterpret_cast<pointer>(memory::allocate(static_cast<std::size_t>(rhs.m_capacity) * sizeof(value_type)));
                buffvec_detail::move_into(buffer, lhs.m_data, lhs.m_size);

                // this could potentially be optimized by considering that we can move-assign to those objects that already exist
                buffvec_detail::destroy(lhs.m_data, lhs.m_data + lhs.m_size);
                buffvec_detail::move_into(lhs.m_data, rhs.m_data, rhs.m_size);

                buffvec_detail::destroy(rhs.m_data, rhs.m_data + rhs.m_size);
                rhs.m_data = buffer;

                swap(lhs.m_size, rhs.m_size);
            }
        }
    }
    void swap(buffvec& other) { using std::swap; swap(*this, other); }

    // [[nodiscard]] is C++17
    bool empty() const noexcept { return size() == 0; }
    size_type size() const noexcept { return m_size; }
    size_type capacity() const noexcept { return m_capacity; }

    void clear() noexcept {
        buffvec_detail::destroy(begin(), end());
        m_size = 0;
    }

    void resize(size_type count) {
        SASSERT(size() + count >= size() && "overflow check");
        if(size() + count > capacity()) {
            _reserve(std::max(next_capacity(), size() + count));
        }
        auto const ptr = this->ptr();
        auto const size = this->size();
        buffvec_detail::destroy(ptr + count, ptr + size);
        for(size_type i = size; i < count; ++i) {
            ::new(ptr + i) value_type();
        }
        m_size = count;
    }

    void resize(size_type count, value_type const& value) {
        SASSERT(size() + count >= size() && "overflow check");
        if(size() + count > capacity()) {
            _reserve(std::max(next_capacity(), size() + count));
        }
        auto const ptr = this->ptr();
        auto const size = this->size();
        buffvec_detail::destroy(ptr + count, ptr + size);
        for(size_type i = size; i < count; ++i) {
            ::new(ptr + i) value_type(value);
        }
        m_size = count;
    }

private:
    // vector::reserve actually does a expand-only resize as per the old API
    void _reserve(size_type new_capacity) {
        if(capacity() < new_capacity) {
            reallocate(new_capacity);
        }
    }
public:

    void shrink_to_fit() {
        if(m_size <= initial_capacity) {
            if(m_data != reinterpret_cast<pointer>(&m_initial_buffer)) {
                buffvec_detail::move_into(reinterpret_cast<pointer>(&m_initial_buffer), m_data, m_size);
                memory::deallocate(m_data);
                m_data = reinterpret_cast<pointer>(&m_initial_buffer);
            }
        } else {
            if(size() < capacity()) {
                reallocate(m_size);
            }
        }
    }

    reference operator[](size_type index) {
        SASSERT(index < size());
        return ptr()[index];
    }

    const_reference operator[](size_type index) const {
        SASSERT(index < size());
        return ptr()[index];
    }

          iterator           begin()       noexcept { return ptr(); }
    const_iterator           begin() const noexcept { return ptr(); }
    const_iterator          cbegin() const noexcept { return ptr(); }
          iterator           end()         noexcept { return ptr() + size(); }
    const_iterator           end()   const noexcept { return ptr() + size(); }
    const_iterator          cend()   const noexcept { return ptr() + size(); }
          reverse_iterator  rbegin()       noexcept { return static_cast<reverse_iterator>(end()); }
    const_reverse_iterator  rbegin() const noexcept { return static_cast<const_reverse_iterator>(end()); }
    const_reverse_iterator crbegin() const noexcept { return static_cast<const_reverse_iterator>(end()); }
          reverse_iterator  rend()         noexcept { return static_cast<reverse_iterator>(begin()); }
    const_reverse_iterator  rend()   const noexcept { return static_cast<const_reverse_iterator>(begin()); }
    const_reverse_iterator crend()   const noexcept { return static_cast<const_reverse_iterator>(begin()); }
    pointer data() noexcept { return ptr(); }
    const_pointer data() const noexcept { return ptr(); }

    reference front() { 
        SASSERT(!empty()); 
        return begin()[0]; 
    }

    const_reference front() const { 
        SASSERT(!empty()); 
        return begin()[0]; 
    }

    reference back() { 
        SASSERT(!empty()); 
        return end()[-1]; 
    }

    const_reference back() const { 
        SASSERT(!empty()); 
        return end()[-1]; 
    }

    void push_back(value_type const& value) {
        auto const size = this->size();
        if(size >= capacity()) {
            reallocate(next_capacity());
        }
        ::new(ptr() + size) value_type(value);
        ++m_size;
    }

    void push_back(value_type&& value) {
        auto const size = this->size();
        if(size >= capacity()) {
            reallocate(next_capacity());
        }
        ::new(ptr() + size) value_type(std::move(value));
        ++m_size;
    }

    template<typename... Args>
    void emplace_back(Args&&... args) {
        auto const size = this->size();
        if(size >= capacity()) {
            reallocate(next_capacity());
        }
        ::new(ptr() + size) value_type(std::forward<Args>(args)...);
        ++m_size;
    }

    void pop_back() {
        SASSERT(!empty()); 
        ptr()[size() - 1].~value_type();
        --m_size;
    }

    // adaptors for the old buffer interface
    void reset() noexcept { clear(); }
    void finalize() { clear(); shrink_to_fit(); }
    reference get(size_type index) { return (*this)[index]; }
    const_reference get(size_type index) const { return (*this)[index]; }
    void set(size_type index, value_type const& value) { (*this)[index] = value; }
    void shrink(size_type count) {
        SASSERT(count <= size());
        resize(count);
    }

    pointer c_ptr() const { return m_data; } // breaks logical const-ness, prefer data() [which is disabled due to the data type]

    void append(size_type count, T const * elements) {
        SASSERT(size() + count >= size() && "overflow check");
        if(size() + count > capacity()) {
            _reserve(std::max(next_capacity(), size() + count));
        }
        buffvec_detail::copy_into(ptr() + size(), elements, count);
        m_size += count;
    }

    void append(const buffvec& source) {
        append(source.size(), source.ptr());
    }
};

//----------------------------- vector that stores its size and capacity locally and data on the heap -----------------------------//
template<typename T, typename SZ>
class buffvec<T, SZ, 0> {
    static_assert(std::numeric_limits<SZ>::is_integer, "SZ must be an unsigned integer type of reasonable size");
    static_assert(!std::numeric_limits<SZ>::is_signed, "SZ must be an unsigned integer type of reasonable size");
    static_assert(std::numeric_limits<SZ>::digits >= 8, "SZ must be an unsigned integer type of reasonable size");
    static_assert(std::numeric_limits<SZ>::digits <= std::numeric_limits<std::size_t>::digits, "SZ must be an unsigned integer type of reasonable size");

public:
    using value_type = T;
    using size_type = SZ;
    using difference_type = std::ptrdiff_t;
    using reference = value_type&;
    using const_reference = value_type const&;
    using pointer = value_type*;
    using const_pointer = value_type const*;
    using iterator = pointer;
    using const_iterator = const_pointer;
    using reverse_iterator = std::reverse_iterator<iterator>;
    using const_reverse_iterator = std::reverse_iterator<const_iterator>;

    static constexpr const size_type initial_capacity = 0;

private:
    pointer m_data = nullptr;
    size_type m_size = 0;
    size_type m_capacity = 0;

    // ptr should really be public and called "data"
    pointer ptr() noexcept { return m_data; }
    const_pointer ptr() const noexcept { return m_data; }

    inline size_type next_capacity() const noexcept {
        auto const cap = capacity();
        return cap == 0 ? 2 : (3 * cap + 1) / 2;
    }

    template<typename U = value_type>
    typename std::enable_if<std::is_trivially_move_constructible<typename std::remove_cv<U>::type>::value && std::is_trivially_destructible<typename std::remove_cv<U>::type>::value>::type
    reallocate(size_type const new_capacity) {
        SASSERT(new_capacity >= size());
        SASSERT(new_capacity > 0);
        std::size_t const new_bytesize = static_cast<std::size_t>(new_capacity) * sizeof(value_type);
        if(m_data == nullptr) { // memory::reallocate does not support realloc(0)
            m_data = reinterpret_cast<pointer>(memory::allocate(new_bytesize));
            m_capacity = new_capacity;
        } else {
            m_data = reinterpret_cast<pointer>(memory::reallocate(m_data, new_bytesize));
            m_capacity = new_capacity;
        }
    }

    template<typename U = value_type>
    typename std::enable_if<!std::is_trivially_move_constructible<typename std::remove_cv<U>::type>::value || !std::is_trivially_destructible<typename std::remove_cv<U>::type>::value>::type
    reallocate(size_type new_capacity) {
        SASSERT(new_capacity >= size());
        SASSERT(new_capacity > 0);
        std::size_t const new_bytesize = static_cast<std::size_t>(new_capacity) * sizeof(value_type);
        auto const new_data = reinterpret_cast<pointer>(memory::allocate(new_bytesize));
        buffvec_detail::move_into(new_data, m_data, m_size);
        buffvec_detail::destroy(m_data, m_data + m_size);
        if(m_data) { // TODO: check if memory::deallocate supports free(nullptr)
            memory::deallocate(m_data);
        }
        m_data = new_data;
        m_capacity = new_capacity;
    }

public:
    constexpr buffvec() noexcept = default;

    buffvec(buffvec const& other) {
        auto const size = other.m_size;
        if(size > 0) {
            reallocate(size);
            buffvec_detail::copy_into(ptr(), other.ptr(), size);
            m_size = size;
        }
    }

    buffvec& operator=(buffvec const& other) {
        if(this != &other) {
            clear();
            auto const size = other.m_size;
            if(size > 0) {
                reallocate(size);
                buffvec_detail::copy_into(ptr(), other.ptr(), size);
                m_size = size;
            }
        }
        return *this;
    }

    buffvec(buffvec&& other) : m_data(other.m_data), m_size(other.m_size), m_capacity(other.m_capacity) {
        other.m_data = nullptr;
        other.m_size = 0;
        other.m_capacity = 0;
    }

    buffvec& operator=(buffvec&& other) {
        using std::swap;
        swap(m_data, other.m_data);
        swap(m_size, other.m_size);
        swap(m_capacity, other.m_capacity);
        return *this;
    }

    friend void swap(buffvec& lhs, buffvec& rhs) {
        using std::swap;
        swap(lhs.m_data, rhs.m_data);
        swap(lhs.m_size, rhs.m_size);
        swap(lhs.m_capacity, rhs.m_capacity);
    }
    void swap(buffvec& other) { using std::swap; swap(*this, other); }

    ~buffvec() {
        if(m_data) { // memory::deallocate does not support passing null pointers
            buffvec_detail::destroy(begin(), end());
            memory::deallocate(m_data);
            m_data = nullptr;
            m_size = 0;
            m_capacity = 0;
        }
    }

    // FIXME: src/muz/pdr/pdr_context.cpp relies on this constructor being implicit
    /* explicit */ buffvec(size_type count) { resize(count); }
    buffvec(size_type count, value_type const& element) { resize(count, element); }
    buffvec(size_type count, const_pointer elements) {
        if(count > 0) {
            reallocate(count);
            buffvec_detail::copy_into(ptr(), elements, count);
            m_size = count;
        }
    }

    // [[nodiscard]] is C++17
    bool empty() const noexcept { return size() == 0; }
    size_type size() const noexcept { return m_size; }
    size_type capacity() const noexcept { return m_capacity; }

    void clear() noexcept {
        buffvec_detail::destroy(ptr(), ptr() + size());
        m_size = 0;
    }

    void resize(size_type count) {
        SASSERT(size() + count >= size() && "overflow check");
        if(size() + count > capacity()) {
            _reserve(std::max(next_capacity(), size() + count));
        }
        buffvec_detail::destroy(ptr() + count, ptr() + size());
        for(size_type i = size(); i < count; ++i) {
            ::new(ptr() + i) value_type();
        }
        m_size = count;
    }

    void resize(size_type count, value_type const& value) {
        SASSERT(size() + count >= size() && "overflow check");
        if(size() + count > capacity()) {
            _reserve(std::max(next_capacity(), size() + count));
        }
        buffvec_detail::destroy(ptr() + count, ptr() + size());
        for(size_type i = size(); i < count; ++i) {
            ::new(ptr() + i) value_type(value);
        }
        m_size = count;
    }

    // vector::reserve actually does an enlarge-only resize as per the old API
private:
    void _reserve(size_type new_capacity) {
        if(new_capacity > capacity()) {
            reallocate(new_capacity);
        }
    }
public:

    void shrink_to_fit() {
        if(size() > 0) {
            if(size() != capacity()) {
                reallocate(size());
            }
        } else {
            if(m_data) {
                memory::deallocate(m_data);
                m_data = nullptr;
                m_capacity = 0;
            }
        }
    }

    reference operator[](size_type index) {
        SASSERT(index < size());
        return ptr()[index];
    }

    const_reference operator[](size_type index) const {
        SASSERT(index < size());
        return ptr()[index];
    }

          iterator           begin()       noexcept { return ptr(); }
    const_iterator           begin() const noexcept { return ptr(); }
    const_iterator          cbegin() const noexcept { return ptr(); }
          iterator           end()         noexcept { return ptr() + size(); }
    const_iterator           end()   const noexcept { return ptr() + size(); }
    const_iterator          cend()   const noexcept { return ptr() + size(); }
          reverse_iterator  rbegin()       noexcept { return static_cast<reverse_iterator>(end()); }
    const_reverse_iterator  rbegin() const noexcept { return static_cast<const_reverse_iterator>(end()); }
    const_reverse_iterator crbegin() const noexcept { return static_cast<const_reverse_iterator>(end()); }
          reverse_iterator  rend()         noexcept { return static_cast<reverse_iterator>(begin()); }
    const_reverse_iterator  rend()   const noexcept { return static_cast<const_reverse_iterator>(begin()); }
    const_reverse_iterator crend()   const noexcept { return static_cast<const_reverse_iterator>(begin()); }
    // interferes with the data member type
    // pointer data() noexcept { return ptr(); }
    // const_pointer data() const noexcept { return ptr(); }

    reference front() { 
        SASSERT(!empty()); 
        return begin()[0]; 
    }

    const_reference front() const { 
        SASSERT(!empty()); 
        return begin()[0]; 
    }

    reference back() { 
        SASSERT(!empty()); 
        return end()[-1]; 
    }

    const_reference back() const { 
        SASSERT(!empty()); 
        return end()[-1]; 
    }

    void push_back(value_type const& value) {
        if(size() >= capacity()) {
            reallocate(next_capacity());
        }
        ::new(ptr() + size()) value_type(value);
        ++m_size;
    }

    void push_back(value_type&& value) {
        if(size() >= capacity()) {
            reallocate(next_capacity());
        }
        ::new(ptr() + size()) value_type(std::move(value));
        ++m_size;
    }

    template<typename... Args>
    void emplace_back(Args&&... args) {
        if(size() >= capacity()) {
            reallocate(next_capacity());
        }
        ::new(ptr() + size()) value_type(std::forward<Args>(args)...);
        ++m_size;
    }

    void pop_back() {
        SASSERT(!empty()); 
        ptr()[size() - 1].~value_type();
        --m_size;
    }

    iterator erase(const_iterator position) {
        auto const iterdiff = position - begin();
        SASSERT(iterdiff >= 0);
        SASSERT(static_cast<std::size_t>(iterdiff) < size());
        auto const index = static_cast<size_type>(iterdiff);

        ptr()[index].~value_type();
        buffvec_detail::move_around(ptr() + index, ptr() + index + 1, size() - index - 1);
        --m_size;
        return ptr() + index;
    }

    iterator erase(value_type const& element) {
        iterator it = std::find(begin(), end(), element);
        if(it != end()) {
            return erase(it);
        }
        return end();
    }

    // adaptors for the old vector interface
    using data = value_type;
    pointer c_ptr() const { return m_data; }
    void reset() noexcept { clear(); }
    void finalize() { clear(); shrink_to_fit(); }
    reference get(size_type index) { return (*this)[index]; }
    const_reference get(size_type index) const { return (*this)[index]; }
    const_reference get(size_type index, T const& default_value) const { return index < size() ? (*this)[index] : default_value; }
    void set(size_type index, T const& new_value) { (*this)[index] = new_value; }
    void setx(size_type index, T const& new_value, T const& default_value) {
        if(index >= size()) {
            SASSERT(index + 1 > 0 && "overflow check");
            if(index + 1 > capacity()) {
                _reserve(std::max(next_capacity(), index + 1));
            }
            for(size_type i = size(); i < index; ++i) {
                ::new(ptr() + i) value_type(default_value);
            }
            new(ptr() + index) value_type(new_value);
            m_size = index + 1;
        } else {
            (*this)[index] = new_value;
        }
    }
    void fill(T const& new_value) { std::fill(begin(), end(), new_value); }
    void fill(size_type new_size, T const& new_value) { resize(new_size); std::fill(begin(), end(), new_value); }
    void reverse() { std::reverse(begin(), end()); }
    void set_end(const_iterator new_end) {
        SASSERT(new_end >= begin() && new_end <= end());
        size_type const new_size = static_cast<size_type>(new_end - begin());
        buffvec_detail::destroy(begin() + new_size, end());
        m_size = new_size;
    }
    bool contains(value_type const& value) const {
        return std::find(begin(), end(), value) != end();
    }

    void reserve(size_type new_size) {
        if(new_size > size()) {
            resize(new_size);
        }
    }
    void insert(value_type const& element) { push_back(element); }

    void reserve(size_type new_size, value_type const& new_value) {
        if(new_size > size()) {
            resize(new_size, new_value);
        }
    }
    template<typename... Args>
    void resize(size_type count, Args const&... args) {
        SASSERT(size() + count >= size() && "overflow check");
        if(size() + count > capacity()) {
            _reserve(std::max(next_capacity(), size() + count));
        }
        buffvec_detail::destroy(ptr() + count, ptr() + size());
        for(size_type i = size(); i < count; ++i) {
            ::new(ptr() + i) value_type(args...);
        }
        m_size = count;
    }
    void shrink(size_type count) {
        SASSERT(count <= size());
        buffvec_detail::destroy(ptr() + count, ptr() + size());
        m_size = count;
    }

    void append(size_type count, T const * elements) {
        SASSERT(size() + count >= size() && "overflow check");
        if(size() + count > capacity()) {
            _reserve(std::max(next_capacity(), size() + count));
        }
        buffvec_detail::copy_into(ptr() + size(), elements, count);
        m_size += count;
    }

    void append(const buffvec& source) {
        append(source.size(), source.ptr());
    }
};


template<typename T1, typename SZ1, std::size_t INITIAL_CAPACITY1, typename T2, typename SZ2, std::size_t INITIAL_CAPACITY2>
bool operator==(buffvec<T1, SZ1, INITIAL_CAPACITY1> const& lhs, buffvec<T2, SZ2, INITIAL_CAPACITY2> const& rhs) {
    if(lhs.size() != rhs.size()) {
        return false;
    }
    auto li = lhs.cbegin();
    auto lend = lhs.cend();
    auto ri = rhs.cbegin();
    for( ; li != lend; ++li, ++ri) {
        if(*li != *ri) {
            return false;
        }
    }
    SASSERT(ri == rhs.cend());
    return true;
}

template<typename T1, typename SZ1, std::size_t INITIAL_CAPACITY1, typename T2, typename SZ2, std::size_t INITIAL_CAPACITY2>
bool operator!=(buffvec<T1, SZ1, INITIAL_CAPACITY1> const& lhs, buffvec<T2, SZ2, INITIAL_CAPACITY2> const& rhs) {
    return !(lhs == rhs);
}

template<typename T1, typename SZ1, std::size_t INITIAL_CAPACITY1, typename T2, typename SZ2, std::size_t INITIAL_CAPACITY2>
bool operator< (buffvec<T1, SZ1, INITIAL_CAPACITY1> const& lhs, buffvec<T2, SZ2, INITIAL_CAPACITY2> const& rhs) {
    return std::lexicographical_compare(lhs.cbegin(), lhs.cend(), rhs.cbegin(), rhs.cend(), [](T1 const& lhs, T2 const& rhs) -> bool { return lhs < rhs; });
}

template<typename T1, typename SZ1, std::size_t INITIAL_CAPACITY1, typename T2, typename SZ2, std::size_t INITIAL_CAPACITY2>
bool operator<=(buffvec<T1, SZ1, INITIAL_CAPACITY1> const& lhs, buffvec<T2, SZ2, INITIAL_CAPACITY2> const& rhs) {
    return std::lexicographical_compare(lhs.cbegin(), lhs.cend(), rhs.cbegin(), rhs.cend(), [](T1 const& lhs, T2 const& rhs) -> bool { return lhs <= rhs; });
}

template<typename T1, typename SZ1, std::size_t INITIAL_CAPACITY1, typename T2, typename SZ2, std::size_t INITIAL_CAPACITY2>
bool operator> (buffvec<T1, SZ1, INITIAL_CAPACITY1> const& lhs, buffvec<T2, SZ2, INITIAL_CAPACITY2> const& rhs) {
    return std::lexicographical_compare(lhs.cbegin(), lhs.cend(), rhs.cbegin(), rhs.cend(), [](T1 const& lhs, T2 const& rhs) -> bool { return lhs > rhs; });
}

template<typename T1, typename SZ1, std::size_t INITIAL_CAPACITY1, typename T2, typename SZ2, std::size_t INITIAL_CAPACITY2>
bool operator>=(buffvec<T1, SZ1, INITIAL_CAPACITY1> const& lhs, buffvec<T2, SZ2, INITIAL_CAPACITY2> const& rhs) {
    return std::lexicographical_compare(lhs.cbegin(), lhs.cend(), rhs.cbegin(), rhs.cend(), [](T1 const& lhs, T2 const& rhs) -> bool { return lhs >= rhs; });
}

namespace std {
    template<typename T, typename SZ, std::size_t INITIAL_CAPACITY>
    struct hash<::buffvec<T, SZ, INITIAL_CAPACITY>> {
        // investigate `get_composite_hash`
        using argument_type = ::buffvec<T, SZ, INITIAL_CAPACITY>;
        using result_type = ::std::size_t;
        result_type operator()(argument_type const& value) const {
            result_type result = ::std::hash<typename argument_type::size_type>()(value.size());
            ::std::hash<typename argument_type::value_type> hasher;
            for(auto const& element : value) {
                static_assert(::std::numeric_limits<result_type>::digits > 11, "Something has gone horribly wrong");
                result = (result << 11) | (result >> (::std::numeric_limits<result_type>::digits - 11));
                result ^= hasher(element);
            }
            return result;
        }
    };
}
