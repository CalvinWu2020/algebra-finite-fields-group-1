// Checks the cached FiniteField against the original algorithm (raw polynomial
// arithmetic reduced by the modulus) on every input of GF(11^3).
#include <cstdint>
#include <stdexcept>
#include <gtest/gtest.h>
#include <algebra/finite_fields/finite_fields.hpp>

using namespace algebra;

namespace {

using F = FiniteField<11, 3>;
using E = F::Element;
using Poly = F::PolynomialType;
const std::uint64_t n = F::cardinality();  // 1331
static_assert(sizeof(E) == 2, "each element should be just its 2-byte index");

// The original algorithm: polynomial math, then reduce by the modulus. Never touches the caches.
Poly reduce(const Poly& p) {
    return p % F::modulus();
}

}

// Pass 1 fills the caches (every call is a miss). Pass 2 reads them back (every call is a hit).
TEST(CachedEquivalence, AddAndMultiplyMatchOriginalOnEveryPair) {
    for (int pass = 1; pass <= 2; ++pass) {
        for (std::uint64_t i = 0; i < n; ++i) {
            const E a = E::from_index(i);
            for (std::uint64_t j = 0; j < n; ++j) {
                const E b = E::from_index(j);
                ASSERT_EQ(a.add(b).representative(), reduce(a.representative() + b.representative()))
                    << "add " << i << " " << j << " pass " << pass;
                ASSERT_EQ(a.multiply(b).representative(), reduce(a.representative() * b.representative()))
                    << "multiply " << i << " " << j << " pass " << pass;
            }
        }
    }
}

TEST(CachedEquivalence, NegateAndReciprocalMatchOriginalOnEveryElement) {
    for (int pass = 1; pass <= 2; ++pass) {
        for (std::uint64_t i = 0; i < n; ++i) {
            const E a = E::from_index(i);
            ASSERT_EQ(a.negate().representative(), reduce(-a.representative())) << "negate " << i;
            if (i != 0) {
                ASSERT_TRUE(reduce(a.representative() * a.reciprocal().representative()) == Poly::one())
                    << "reciprocal " << i;
            }
        }
    }
    EXPECT_THROW(E::zero().reciprocal(), std::domain_error);
}

TEST(CachedEquivalence, IndexRoundTripsForEveryElement) {
    for (std::uint64_t i = 0; i < n; ++i) {
        const E a = E::from_index(i);
        ASSERT_EQ(a.to_index(), i);
        ASSERT_EQ(E::from_polynomial(a.representative()), a);
    }
    EXPECT_TRUE(E::zero().is_zero());
    EXPECT_TRUE(E::one().is_one());
}