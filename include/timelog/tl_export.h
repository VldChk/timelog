#ifndef TL_EXPORT_H
#define TL_EXPORT_H

#if defined(TL_BUILD_SHARED)
  #if defined(_WIN32) || defined(__CYGWIN__)
    #if defined(TL_EXPORTS)
      #define TL_API __declspec(dllexport)
    #else
      #define TL_API __declspec(dllimport)
    #endif
  #elif defined(__GNUC__) && (__GNUC__ >= 4)
    #define TL_API __attribute__((visibility("default")))
  #else
    #define TL_API
  #endif
#else
  #define TL_API
#endif

#endif /* TL_EXPORT_H */
