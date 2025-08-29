# Quantifier Instantiation Callbacks Podcast Generator

This Genaiscript generates engaging podcast scripts about Z3's quantifier instantiation callback feature added in version 4.15.3.

## Usage

To generate a podcast script, run:

```bash
# Default conversational style, medium duration (15-20 min)
genaiscript run quantifier_callbacks_podcast

# Educational style, short duration (5-10 min)  
genaiscript run quantifier_callbacks_podcast --vars style=educational duration=short

# Technical style, long duration (25-30 min)
genaiscript run quantifier_callbacks_podcast --vars style=technical duration=long
```

## Parameters

- **style**: `conversational` (default), `technical`, or `educational`
  - `conversational`: Friendly, accessible tone with analogies
  - `technical`: Precise terminology for experienced developers  
  - `educational`: Step-by-step learning approach

- **duration**: `short`, `medium` (default), or `long`
  - `short`: 5-10 minutes of content
  - `medium`: 15-20 minutes of content
  - `long`: 25-30 minutes of content

## Output

The script generates a complete podcast episode covering:

- Introduction to quantifier instantiation callbacks
- Why this feature is important
- Practical usage examples in Python, C++, and C
- Advanced use cases and patterns
- Implementation guidance

## Source Material

The podcast script is generated from:
- `doc/quantifier_instantiation_callback.md` - Complete API documentation
- `examples/python/quantifier_instantiation_callback.py` - Python examples
- `examples/c++/quantifier_instantiation_callback.cpp` - C++ examples
- `examples/README_quantifier_callbacks.md` - Usage guide

This ensures technical accuracy and comprehensive coverage of the feature.