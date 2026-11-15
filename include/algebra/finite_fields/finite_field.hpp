#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <ostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>
#include <utility>
#include <algebra/finite_fields/modulus.hpp>

namespace algebra {

template<std::uint32_t P, std::size_t K = 1, class ModulusPolicy = FirstEnumeratedIrreducible>
class FiniteField;

template<std::uint32_t P, std::size_t K, class ModulusPolicy>
class FiniteFieldElement : public AdditiveOperators<FiniteFieldElement<P, K, ModulusPolicy>>,
                           public MultiplicativeOperators<FiniteFieldElement<P, K, ModulusPolicy>>,
                           public DivisionOperators<FiniteFieldElement<P, K, ModulusPolicy>> {
    static_assert(is_prime(P));
    static_assert(K > 0);

public:
    using parent_type = FiniteField<P, K, ModulusPolicy>;
    using algebra = FieldDescriptor;
    using coefficient_type = PrimeFieldElement<P>;
    using polynomial_type = Polynomial<coefficient_type>;

private:
    std::uint32_t index_ = 0;  // which element this is: same numbering as from_index / to_index
    struct Reduced {};

    FiniteFieldElement(std::uint32_t index, Reduced) : index_(index) {}

    // this element's reduced polynomial, looked up in a table built once per field
    const polynomial_type& value() const {
        return parent_type::polynomials()[index_];
    }

    // reverse of from_index for an already-reduced polynomial
    static std::uint32_t encode(const polynomial_type& reduced) {
        std::uint32_t index = 0;
        std::uint32_t place = 1;
        for (std::size_t i = 0; i < K; ++i) {
            index += reduced.coefficient(i).representative() * place;
            place *= P;
        }
        return index;
    }

public:
    FiniteFieldElement() {
        static_cast<void>(parent_type::modulus());
    }

    static FiniteFieldElement from_polynomial(const polynomial_type& value) {
        const polynomial_type remainder = value % parent_type::modulus();
        return FiniteFieldElement(encode(remainder), Reduced{});
    }

    static FiniteFieldElement from_coefficients(std::initializer_list<std::int64_t> values) {
        polynomial_type value;
        std::size_t index = 0;
        for (const auto coefficient : values) {
            value.set_coefficient(index++, coefficient_type::from_integer(coefficient));
        }
        return from_polynomial(value);
    }

    static FiniteFieldElement from_integer(std::int64_t value) {
        return from_polynomial(polynomial_type{coefficient_type::from_integer(value)});
    }

    static FiniteFieldElement from_index(std::uint64_t index) {
        if (index >= parent_type::cardinality()) {
            throw std::out_of_range("Finite field element index is out of range");
        }
        polynomial_type value;
        for (std::size_t i = 0; i < K; ++i) {
            value.set_coefficient(i, coefficient_type::from_index(index % P));
            index /= P;
        }
        return from_polynomial(value);
    }

    // reverse of from_index, used for hashing
    std::uint64_t to_index() const {
        return index_;
    }

    static FiniteFieldElement zero() {
        return FiniteFieldElement{};
    }

    static FiniteFieldElement one() {
        return from_integer(1);
    }

    FiniteFieldElement add(const FiniteFieldElement& other) const {
        auto& cache = parent_type::opcache_add;
        auto& known = parent_type::opknown_add;
        const std::uint64_t key = to_index() * parent_type::cardinality() + other.to_index();
        if (cache.empty()) {  // first use: one slot per (a, b) pair
            cache.resize(parent_type::cardinality() * parent_type::cardinality());
            known.assign(cache.size(), false);
        }

        if (known[key]) return FiniteFieldElement(cache[key], Reduced{});

        const polynomial_type sum = value().add(other.value());
        FiniteFieldElement result = from_polynomial(sum);
        cache[key] = result.index_;
        known[key] = true;
        return result;
    }

    FiniteFieldElement negate() const {
        auto& cache = parent_type::opcache_negate;
        auto& known = parent_type::opknown_negate;
        if (cache.empty()) {  // first use: one slot per element
            cache.resize(parent_type::cardinality());
            known.assign(cache.size(), false);
        }

        if (known[index_]) return FiniteFieldElement(cache[index_], Reduced{});

        FiniteFieldElement result = from_polynomial(value().negate());
        cache[index_] = result.index_;
        known[index_] = true;
        return result;
    }

    FiniteFieldElement multiply(const FiniteFieldElement& other) const {
        auto& cache = parent_type::opcache_multiply;
        auto& known = parent_type::opknown_multiply;
        const std::uint64_t key = to_index() * parent_type::cardinality() + other.to_index();
        if (cache.empty()) {  // first use: one slot per (a, b) pair
            cache.resize(parent_type::cardinality() * parent_type::cardinality());
            known.assign(cache.size(), false);
        }

        if (known[key]) return FiniteFieldElement(cache[key], Reduced{});

        const polynomial_type product = value().multiply(other.value());
        FiniteFieldElement result = from_polynomial(product);
        cache[key] = result.index_;
        known[key] = true;
        return result;
    }

    FiniteFieldElement reciprocal() const {
        if (is_zero()) {
            throw std::domain_error("Zero has no reciprocal");
        }

        auto& cache = parent_type::opcache_reciprocal;
        auto& known = parent_type::opknown_reciprocal;
        if (cache.empty()) {  // first use: one slot per element
            cache.resize(parent_type::cardinality());
            known.assign(cache.size(), false);
        }

        if (known[index_]) return FiniteFieldElement(cache[index_], Reduced{});

        polynomial_type previous_remainder = parent_type::modulus();
        polynomial_type remainder = value();
        polynomial_type previous_coefficient = polynomial_type::zero();
        polynomial_type coefficient = polynomial_type::one();
        while (!remainder.is_zero()) {
            auto division = previous_remainder.divmod(remainder);
            polynomial_type next_remainder = std::move(division.second);
            polynomial_type next_coefficient =
                previous_coefficient - division.first.multiply(coefficient);
            previous_remainder = std::move(remainder);
            remainder = std::move(next_remainder);
            previous_coefficient = std::move(coefficient);
            coefficient = std::move(next_coefficient);
        }
        if (previous_remainder.degree() != 0) {
            throw std::logic_error("The element is not invertible for this modulus");
        }
        const coefficient_type scale = previous_remainder.coefficient(0).reciprocal();
        FiniteFieldElement result = from_polynomial(previous_coefficient.scale_left(scale));

        cache[index_] = result.index_;
        known[index_] = true;
        return result;
    }

    bool is_zero() const {
        return index_ == 0;
    }

    bool is_one() const {
        return index_ == 1;
    }

    coefficient_type coefficient(std::size_t index) const {
        if (index >= K) {
            throw std::out_of_range("Finite field coefficient index is out of range");
        }
        return value().coefficient(index);
    }

    std::array<coefficient_type, K> coefficients() const {
        std::array<coefficient_type, K> result{};
        for (std::size_t i = 0; i < K; ++i) {
            result[i] = value().coefficient(i);
        }
        return result;
    }

    const polynomial_type& representative() const {
        return value();
    }

    const parent_type& parent() const {
        static const parent_type instance;
        return instance;
    }

    bool operator==(const FiniteFieldElement& other) const {
        return index_ == other.index_;
    }

    friend std::ostream& operator<<(std::ostream& out, const FiniteFieldElement& value) {
        return out << value.value();
    }

    // custom hashing functor to allow this class to be used as a key in unordered_map
    struct Hash {
        std::size_t operator()(const FiniteFieldElement& elem) const noexcept {
            return static_cast<std::size_t>(elem.to_index());
        }
    };
};

template<std::uint32_t P, std::size_t K, class ModulusPolicy>
class FiniteField : public FieldStructure<FiniteFieldElement<P, K, ModulusPolicy>> {
    static_assert(is_prime(P));
    static_assert(K > 0);

public:
    // moved these up here
    using Element = FiniteFieldElement<P, K, ModulusPolicy>;
    using Base = PrimeField<Cyclic<P>>;
    using PolynomialType = typename Element::polynomial_type;

private:
    // alias for hash struct functor
    using ElementHash = typename Element::Hash;

    // every reduced polynomial in the field, in from_index order (element i is polynomials()[i])
    static const std::vector<PolynomialType>& polynomials() {
        static const std::vector<PolynomialType> table = [] {
            std::vector<PolynomialType> all(static_cast<std::size_t>(cardinality()));
            for (std::size_t i = 0; i < all.size(); ++i) {
                std::uint64_t digits = i;
                for (std::size_t d = 0; d < K; ++d) {
                    all[i].set_coefficient(d, Element::coefficient_type::from_index(digits % P));
                    digits /= P;
                }
            }
            return all;
        }();
        return table;
    }

    // operation caches: each slot holds the result's index, must be static because of how the template class is designed
    inline static std::vector<std::uint32_t> opcache_add;
    inline static std::vector<bool> opknown_add;
    inline static std::vector<std::uint32_t> opcache_multiply;
    inline static std::vector<bool> opknown_multiply;
    inline static std::vector<std::uint32_t> opcache_negate;
    inline static std::vector<bool> opknown_negate;
    inline static std::vector<std::uint32_t> opcache_reciprocal;
    inline static std::vector<bool> opknown_reciprocal;

    friend Element;  // allows the finite field element to access these (if we add more priv fields, might rethink this)

public:
    static constexpr std::uint32_t characteristic = P;
    static constexpr std::size_t extension_degree = K;

    FiniteField() {
        initialize();
    }

    static const PolynomialType& modulus() {
        static const PolynomialType value = [] {
            PolynomialType candidate = ModulusPolicy::template polynomial<P, K>();
            if (candidate.degree() != K || !candidate.leading_coefficient().is_one() ||
                !is_irreducible(candidate)) {
                throw std::invalid_argument("The modulus must be monic and irreducible with degree K");
            }
            return candidate;
        }();
        return value;
    }

    static void initialize() {
        static_cast<void>(modulus());
    }

    static std::uint64_t cardinality() {
        return checked_power(P, K);
    }

    static Element element(std::initializer_list<std::int64_t> values) {
        return Element::from_coefficients(values);
    }

    static Element element(std::int64_t value) {
        return Element::from_integer(value);
    }

    static Element zero() {
        return Element::zero();
    }

    static Element one() {
        return Element::one();
    }

    static Element alpha() {
        return Element::from_polynomial(PolynomialType::variable());
    }
};

}
