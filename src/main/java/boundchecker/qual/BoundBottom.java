package boundchecker.qual;

import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

/**
 * @author Tianhan Lu
 */
@SubtypeOf({BoundTop.class})
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@Documented
public @interface BoundBottom {
}
