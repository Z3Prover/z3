#pragma once

#include "util/debug.h"

#include <cstddef>
#include <utility>
#include <array>

template<typename T>
class buffer_view {

public:
    using value_type = T;
    using size_type = std::size_t;
    using difference_type = std::ptrdiff_t;
    using reference = value_type&;
    using const_reference = value_type const&;
    using pointer = value_type*;
    using const_pointer = value_type const*;
    using iterator = pointer;
    using const_iterator = const_pointer;
    using reverse_iterator = std::reverse_iterator<iterator>;
    using const_reverse_iterator = std::reverse_iterator<const_iterator>;

private:
    const_pointer m_data = nullptr;
    size_type m_size = 0;

public:
    constexpr buffer_view() noexcept = default;
    constexpr buffer_view(buffer_view const& other) noexcept = default;
    buffer_view& operator=(buffer_view const& other) noexcept = default;

    constexpr buffer_view(const_pointer data, size_type size) : m_data(data), m_size(size) { }

    // conversion from arrays
    template<std::size_t SIZE>
    constexpr buffer_view(value_type (&array)[SIZE])
        : m_data(array), m_size(SIZE)
    { }

    template<std::size_t SIZE>
    constexpr buffer_view& operator=(value_type (&array)[SIZE])
    {
        m_data = array;
        m_size = SIZE;
        return *this;
    }

    // conversion from std::array
    template<std::size_t SIZE>
    constexpr buffer_view(std::array<value_type, SIZE> const& array)
        : m_data(array.data()), m_size(array.size())
    { }

    template<std::size_t SIZE>
    constexpr buffer_view& operator=(std::array<value_type, SIZE> const& array)
    {
        m_data = array.data();
        m_size = array.size();
        return *this;
    }

    constexpr size_type size() const noexcept { return m_size; }
    constexpr bool empty() const noexcept { return m_size == 0; }

    constexpr const_reference operator[](size_type index) const {
        SASSERT(index < m_size);
        return m_data(index);
    }

    constexpr const_reference front() const {
        SASSERT(!empty());
        return m_data[0];
    }

    constexpr const_reference back() const {
        SASSERT(!empty());
        return m_data[m_size - 1];
    }

    constexpr const_iterator  begin() const noexcept { return m_data; }
    constexpr const_iterator cbegin() const noexcept { return m_data; }
    constexpr const_iterator  end  () const noexcept { return m_data + m_size; }
    constexpr const_iterator cend  () const noexcept { return m_data + m_size; }
    constexpr const_reverse_iterator  rbegin() const noexcept { return static_cast<const_reverse_iterator>(end()); }
    constexpr const_reverse_iterator rcbegin() const noexcept { return static_cast<const_reverse_iterator>(end()); }
    constexpr const_reverse_iterator  rend  () const noexcept { return static_cast<const_reverse_iterator>(begin()); }
    constexpr const_reverse_iterator rcend  () const noexcept { return static_cast<const_reverse_iterator>(begin()); }
    constexpr const_pointer data() const noexcept { return m_data; }

    constexpr buffer_view subview(size_type begin) const {
        SASSERT(begin <= m_size);
        return buffer_view(m_data + begin, m_size - begin);
    }

    constexpr buffer_view subview(size_type begin, size_type end) const {
        SASSERT(begin + end >= begin && "overflow check");
        SASSERT(begin + end <= m_size);
        return buffer_view(m_data + begin, m_size - (begin + end));
    }
};
