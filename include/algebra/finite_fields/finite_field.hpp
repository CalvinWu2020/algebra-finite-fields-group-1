#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <ostream>
#include <stdexcept>
#include <unordered_map>
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
    polynomial_type value_;
    struct Reduced {};

    FiniteFieldElement(polynomial_type value, Reduced) : value_(std::move(value)) {}

public:
    FiniteFieldElement() {
        static_cast<void>(parent_type::modulus());
    }

    static FiniteFieldElement from_polynomial(const polynomial_type& value) {
        polynomial_type remainder = value % parent_type::modulus();
        return FiniteFieldElement(std::move(remainder), Reduced{});
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
        std::uint64_t index = 0;
        std::uint64_t place = 1;
        for (std::size_t i = 0; i < K; ++i) {
            index += value_.coefficient(i).representative() * place;  // value_.coefficient() produces a RingElement, which needs representative() to get a numeric
            place *= P;
        }
        return index;
    }

    static FiniteFieldElement zero() {
        return FiniteFieldElement{};
    }

    static FiniteFieldElement one() {
        return from_integer(1);
    }

    FiniteFieldElement add(const FiniteFieldElement& other) const {
        auto& cache = parent_type::opcache_add;
        typename parent_type::TwoElementCacheKey key = {*this, other};

        auto found = cache.find(key);
        if (found != cache.end()) return found->second;

        const polynomial_type sum = value_.add(other.value_);
        FiniteFieldElement result = from_polynomial(sum);
        cache.emplace(key, result);
        return result;
    }

    FiniteFieldElement negate() const {
        auto& cache = parent_type::opcache_negate;

        auto found = cache.find(*this);
        if (found != cache.end()) return found->second;

        FiniteFieldElement result = from_polynomial(value_.negate());
        cache.emplace(*this, result);
        return result;
    }

    FiniteFieldElement multiply(const FiniteFieldElement& other) const {
        auto& cache = parent_type::opcache_multiply;
        typename parent_type::TwoElementCacheKey key = {*this, other};

        auto found = cache.find(key);
        if (found != cache.end()) return found->second;

        const polynomial_type product = value_.multiply(other.value_);
        FiniteFieldElement result = from_polynomial(product);
        cache.emplace(key, result);
        return result;
    }

    FiniteFieldElement reciprocal() const {
        if (is_zero()) {
            throw std::domain_error("Zero has no reciprocal");
        }

        auto& cache = parent_type::opcache_reciprocal;

        auto found = cache.find(*this);
        if (found != cache.end()) return found->second;

        polynomial_type previous_remainder = parent_type::modulus();
        polynomial_type remainder = value_;
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

        cache.emplace(*this, result);
        return result;
    }

    bool is_zero() const {
        return value_.is_zero();
    }

    bool is_one() const {
        return value_.is_one();
    }

    coefficient_type coefficient(std::size_t index) const {
        if (index >= K) {
            throw std::out_of_range("Finite field coefficient index is out of range");
        }
        return value_.coefficient(index);
    }

    std::array<coefficient_type, K> coefficients() const {
        std::array<coefficient_type, K> result{};
        for (std::size_t i = 0; i < K; ++i) {
            result[i] = value_.coefficient(i);
        }
        return result;
    }

    const polynomial_type& representative() const {
        return value_;
    }

    const parent_type& parent() const {
        static const parent_type instance;
        return instance;
    }

    bool operator==(const FiniteFieldElement& other) const {
        return value_ == other.value_;
    }

    friend std::ostream& operator<<(std::ostream& out, const FiniteFieldElement& value) {
        return out << value.value_;
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

    // unordered map two-operand key struct
    struct TwoElementCacheKey {
        Element op1;
        Element op2;

        bool operator==(const TwoElementCacheKey& other) const {
            return (op1 == other.op1) && (op2 == other.op2);
        }

        struct Hash {
            std::size_t operator()(const TwoElementCacheKey& key) const noexcept {
                std::size_t h1 = static_cast<std::size_t>(key.op1.to_index());
                std::size_t h2 = static_cast<std::size_t>(key.op2.to_index());
                return h1 + (h2 * P * K);
            }
        };
    };
    using TwoElementCacheKeyHash = typename TwoElementCacheKey::Hash;
    
    // unordered map operation caches, must be static because of how the template class is designed
    inline static std::unordered_map<TwoElementCacheKey, Element, TwoElementCacheKeyHash> opcache_add;
    inline static std::unordered_map<TwoElementCacheKey, Element, TwoElementCacheKeyHash> opcache_multiply;
    inline static std::unordered_map<Element, Element, ElementHash> opcache_negate;
    inline static std::unordered_map<Element, Element, ElementHash> opcache_reciprocal;

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
